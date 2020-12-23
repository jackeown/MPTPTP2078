%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:24 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 253 expanded)
%              Number of leaves         :   31 (  96 expanded)
%              Depth                    :   12
%              Number of atoms          :  130 ( 683 expanded)
%              Number of equality atoms :    8 (  89 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_20,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_64,plain,(
    ! [A_28] :
      ( u1_struct_0(A_28) = k2_struct_0(A_28)
      | ~ l1_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_69,plain,(
    ! [A_29] :
      ( u1_struct_0(A_29) = k2_struct_0(A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(resolution,[status(thm)],[c_20,c_64])).

tff(c_73,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_69])).

tff(c_81,plain,(
    ! [A_32] :
      ( ~ v1_xboole_0(u1_struct_0(A_32))
      | ~ l1_struct_0(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_84,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_81])).

tff(c_85,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_84])).

tff(c_86,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_89,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_86])).

tff(c_93,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_89])).

tff(c_94,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_28,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_48,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_24,plain,(
    ! [A_11] :
      ( v4_pre_topc(k2_struct_0(A_11),A_11)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_75,plain,(
    m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_32])).

tff(c_6,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    ! [A_12] :
      ( v3_pre_topc(k2_struct_0(A_12),A_12)
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_47,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_46,plain,(
    ! [D_24] :
      ( v3_pre_topc(D_24,'#skF_1')
      | ~ r2_hidden(D_24,'#skF_3')
      | ~ m1_subset_1(D_24,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_97,plain,(
    ! [D_33] :
      ( v3_pre_topc(D_33,'#skF_1')
      | ~ r2_hidden(D_33,'#skF_3')
      | ~ m1_subset_1(D_33,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_46])).

tff(c_107,plain,
    ( v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_47,c_97])).

tff(c_140,plain,(
    ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_40,plain,(
    ! [D_24] :
      ( r2_hidden(D_24,'#skF_3')
      | ~ r2_hidden('#skF_2',D_24)
      | ~ v4_pre_topc(D_24,'#skF_1')
      | ~ v3_pre_topc(D_24,'#skF_1')
      | ~ m1_subset_1(D_24,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_215,plain,(
    ! [D_54] :
      ( r2_hidden(D_54,'#skF_3')
      | ~ r2_hidden('#skF_2',D_54)
      | ~ v4_pre_topc(D_54,'#skF_1')
      | ~ v3_pre_topc(D_54,'#skF_1')
      | ~ m1_subset_1(D_54,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_40])).

tff(c_226,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),'#skF_3')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_47,c_215])).

tff(c_231,plain,
    ( ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_226])).

tff(c_241,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_231])).

tff(c_247,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_241])).

tff(c_252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_247])).

tff(c_253,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_231])).

tff(c_255,plain,(
    ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_253])).

tff(c_258,plain,
    ( ~ m1_subset_1('#skF_2',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_255])).

tff(c_261,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_258])).

tff(c_263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_261])).

tff(c_264,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_283,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_264])).

tff(c_288,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_283])).

tff(c_290,plain,(
    r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_291,plain,(
    ! [A_60,C_61,B_62] :
      ( m1_subset_1(A_60,C_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(C_61))
      | ~ r2_hidden(A_60,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_307,plain,(
    ! [A_63,A_64] :
      ( m1_subset_1(A_63,A_64)
      | ~ r2_hidden(A_63,A_64) ) ),
    inference(resolution,[status(thm)],[c_47,c_291])).

tff(c_314,plain,(
    m1_subset_1(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_290,c_307])).

tff(c_10,plain,(
    ! [B_2,A_1] :
      ( v1_xboole_0(B_2)
      | ~ m1_subset_1(B_2,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_332,plain,
    ( v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_314,c_10])).

tff(c_335,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_332])).

tff(c_337,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_335])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:51:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.26  
% 2.21/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.26  %$ v4_pre_topc > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.21/1.26  
% 2.21/1.26  %Foreground sorts:
% 2.21/1.26  
% 2.21/1.26  
% 2.21/1.26  %Background operators:
% 2.21/1.26  
% 2.21/1.26  
% 2.21/1.26  %Foreground operators:
% 2.21/1.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.21/1.26  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.21/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.21/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.26  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.21/1.26  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.21/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.26  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.21/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.21/1.26  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.21/1.26  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.21/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.21/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.26  
% 2.21/1.28  tff(f_105, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.21/1.28  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.21/1.28  tff(f_53, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.21/1.28  tff(f_65, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.21/1.28  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.21/1.28  tff(f_71, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.21/1.28  tff(f_39, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.21/1.28  tff(f_77, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.21/1.28  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.21/1.28  tff(f_43, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.21/1.28  tff(f_49, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.21/1.28  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.21/1.28  tff(c_20, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.21/1.28  tff(c_38, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.21/1.28  tff(c_64, plain, (![A_28]: (u1_struct_0(A_28)=k2_struct_0(A_28) | ~l1_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.21/1.28  tff(c_69, plain, (![A_29]: (u1_struct_0(A_29)=k2_struct_0(A_29) | ~l1_pre_topc(A_29))), inference(resolution, [status(thm)], [c_20, c_64])).
% 2.21/1.28  tff(c_73, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_69])).
% 2.21/1.28  tff(c_81, plain, (![A_32]: (~v1_xboole_0(u1_struct_0(A_32)) | ~l1_struct_0(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.21/1.28  tff(c_84, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_73, c_81])).
% 2.21/1.28  tff(c_85, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_38, c_84])).
% 2.21/1.28  tff(c_86, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_85])).
% 2.21/1.28  tff(c_89, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_86])).
% 2.21/1.28  tff(c_93, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_89])).
% 2.21/1.28  tff(c_94, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_85])).
% 2.21/1.28  tff(c_28, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.21/1.28  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.21/1.28  tff(c_48, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2])).
% 2.21/1.28  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.21/1.28  tff(c_24, plain, (![A_11]: (v4_pre_topc(k2_struct_0(A_11), A_11) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.21/1.28  tff(c_32, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.21/1.28  tff(c_75, plain, (m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_32])).
% 2.21/1.28  tff(c_6, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.21/1.28  tff(c_26, plain, (![A_12]: (v3_pre_topc(k2_struct_0(A_12), A_12) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.21/1.28  tff(c_12, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.21/1.28  tff(c_14, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.21/1.28  tff(c_47, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 2.21/1.28  tff(c_46, plain, (![D_24]: (v3_pre_topc(D_24, '#skF_1') | ~r2_hidden(D_24, '#skF_3') | ~m1_subset_1(D_24, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.21/1.28  tff(c_97, plain, (![D_33]: (v3_pre_topc(D_33, '#skF_1') | ~r2_hidden(D_33, '#skF_3') | ~m1_subset_1(D_33, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_46])).
% 2.21/1.28  tff(c_107, plain, (v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_47, c_97])).
% 2.21/1.28  tff(c_140, plain, (~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_107])).
% 2.21/1.28  tff(c_40, plain, (![D_24]: (r2_hidden(D_24, '#skF_3') | ~r2_hidden('#skF_2', D_24) | ~v4_pre_topc(D_24, '#skF_1') | ~v3_pre_topc(D_24, '#skF_1') | ~m1_subset_1(D_24, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.21/1.28  tff(c_215, plain, (![D_54]: (r2_hidden(D_54, '#skF_3') | ~r2_hidden('#skF_2', D_54) | ~v4_pre_topc(D_54, '#skF_1') | ~v3_pre_topc(D_54, '#skF_1') | ~m1_subset_1(D_54, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_40])).
% 2.21/1.28  tff(c_226, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_47, c_215])).
% 2.21/1.28  tff(c_231, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_140, c_226])).
% 2.21/1.28  tff(c_241, plain, (~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_231])).
% 2.21/1.28  tff(c_247, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_241])).
% 2.21/1.28  tff(c_252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_247])).
% 2.21/1.28  tff(c_253, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_231])).
% 2.21/1.28  tff(c_255, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_253])).
% 2.21/1.28  tff(c_258, plain, (~m1_subset_1('#skF_2', k2_struct_0('#skF_1')) | v1_xboole_0(k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_255])).
% 2.21/1.28  tff(c_261, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_258])).
% 2.21/1.28  tff(c_263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_261])).
% 2.21/1.28  tff(c_264, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_253])).
% 2.21/1.28  tff(c_283, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_264])).
% 2.21/1.28  tff(c_288, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_283])).
% 2.21/1.28  tff(c_290, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_107])).
% 2.21/1.28  tff(c_291, plain, (![A_60, C_61, B_62]: (m1_subset_1(A_60, C_61) | ~m1_subset_1(B_62, k1_zfmisc_1(C_61)) | ~r2_hidden(A_60, B_62))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.21/1.28  tff(c_307, plain, (![A_63, A_64]: (m1_subset_1(A_63, A_64) | ~r2_hidden(A_63, A_64))), inference(resolution, [status(thm)], [c_47, c_291])).
% 2.21/1.28  tff(c_314, plain, (m1_subset_1(k2_struct_0('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_290, c_307])).
% 2.21/1.28  tff(c_10, plain, (![B_2, A_1]: (v1_xboole_0(B_2) | ~m1_subset_1(B_2, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.21/1.28  tff(c_332, plain, (v1_xboole_0(k2_struct_0('#skF_1')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_314, c_10])).
% 2.21/1.28  tff(c_335, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_332])).
% 2.21/1.28  tff(c_337, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_335])).
% 2.21/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.28  
% 2.21/1.28  Inference rules
% 2.21/1.28  ----------------------
% 2.21/1.28  #Ref     : 0
% 2.21/1.28  #Sup     : 55
% 2.21/1.28  #Fact    : 0
% 2.21/1.28  #Define  : 0
% 2.21/1.28  #Split   : 5
% 2.21/1.28  #Chain   : 0
% 2.21/1.28  #Close   : 0
% 2.21/1.28  
% 2.21/1.28  Ordering : KBO
% 2.21/1.28  
% 2.21/1.28  Simplification rules
% 2.21/1.28  ----------------------
% 2.21/1.28  #Subsume      : 16
% 2.21/1.28  #Demod        : 24
% 2.21/1.28  #Tautology    : 18
% 2.21/1.28  #SimpNegUnit  : 4
% 2.21/1.28  #BackRed      : 2
% 2.21/1.28  
% 2.21/1.28  #Partial instantiations: 0
% 2.21/1.28  #Strategies tried      : 1
% 2.21/1.28  
% 2.21/1.28  Timing (in seconds)
% 2.21/1.28  ----------------------
% 2.21/1.28  Preprocessing        : 0.29
% 2.21/1.28  Parsing              : 0.16
% 2.21/1.28  CNF conversion       : 0.02
% 2.21/1.28  Main loop            : 0.22
% 2.21/1.28  Inferencing          : 0.08
% 2.21/1.28  Reduction            : 0.06
% 2.21/1.28  Demodulation         : 0.04
% 2.21/1.28  BG Simplification    : 0.01
% 2.21/1.28  Subsumption          : 0.04
% 2.21/1.28  Abstraction          : 0.01
% 2.21/1.28  MUC search           : 0.00
% 2.21/1.28  Cooper               : 0.00
% 2.21/1.28  Total                : 0.55
% 2.21/1.28  Index Insertion      : 0.00
% 2.21/1.28  Index Deletion       : 0.00
% 2.21/1.28  Index Matching       : 0.00
% 2.21/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
