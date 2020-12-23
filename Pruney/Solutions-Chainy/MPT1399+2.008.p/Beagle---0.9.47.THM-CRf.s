%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:19 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 251 expanded)
%              Number of leaves         :   34 (  98 expanded)
%              Depth                    :   12
%              Number of atoms          :  139 ( 724 expanded)
%              Number of equality atoms :    8 (  87 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_119,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v3_pre_topc(B,A)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_34,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_34,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,(
    ! [A_2] : r1_tarski('#skF_4',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_22,plain,(
    ! [A_14] :
      ( v4_pre_topc(k2_struct_0(A_14),A_14)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_80,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_85,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_20,c_80])).

tff(c_89,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_85])).

tff(c_154,plain,(
    ! [A_53] :
      ( m1_subset_1('#skF_1'(A_53),k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_160,plain,
    ( m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_154])).

tff(c_163,plain,
    ( m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_160])).

tff(c_164,plain,(
    m1_subset_1('#skF_1'('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_163])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( v1_xboole_0(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_180,plain,
    ( v1_xboole_0('#skF_1'('#skF_2'))
    | ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_164,c_12])).

tff(c_181,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_101,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_38])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24,plain,(
    ! [A_15] :
      ( v3_pre_topc(k2_struct_0(A_15),A_15)
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_53,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_52,plain,(
    ! [D_29] :
      ( v3_pre_topc(D_29,'#skF_2')
      | ~ r2_hidden(D_29,'#skF_4')
      | ~ m1_subset_1(D_29,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_112,plain,(
    ! [D_41] :
      ( v3_pre_topc(D_41,'#skF_2')
      | ~ r2_hidden(D_41,'#skF_4')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_52])).

tff(c_117,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_53,c_112])).

tff(c_131,plain,(
    ~ r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_46,plain,(
    ! [D_29] :
      ( r2_hidden(D_29,'#skF_4')
      | ~ r2_hidden('#skF_3',D_29)
      | ~ v4_pre_topc(D_29,'#skF_2')
      | ~ v3_pre_topc(D_29,'#skF_2')
      | ~ m1_subset_1(D_29,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_183,plain,(
    ! [D_54] :
      ( r2_hidden(D_54,'#skF_4')
      | ~ r2_hidden('#skF_3',D_54)
      | ~ v4_pre_topc(D_54,'#skF_2')
      | ~ v3_pre_topc(D_54,'#skF_2')
      | ~ m1_subset_1(D_54,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_46])).

tff(c_190,plain,
    ( r2_hidden(k2_struct_0('#skF_2'),'#skF_4')
    | ~ r2_hidden('#skF_3',k2_struct_0('#skF_2'))
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_53,c_183])).

tff(c_194,plain,
    ( ~ r2_hidden('#skF_3',k2_struct_0('#skF_2'))
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_190])).

tff(c_208,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_211,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_208])).

tff(c_215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_211])).

tff(c_216,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_218,plain,(
    ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_221,plain,
    ( v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_218])).

tff(c_224,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_221])).

tff(c_226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_224])).

tff(c_227,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_235,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_227])).

tff(c_239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_235])).

tff(c_240,plain,(
    v1_xboole_0('#skF_1'('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_30,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0('#skF_1'(A_16))
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_244,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_240,c_30])).

tff(c_250,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_244])).

tff(c_252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_250])).

tff(c_254,plain,(
    r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( ~ r1_tarski(B_11,A_10)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_264,plain,(
    ~ r1_tarski('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_254,c_16])).

tff(c_268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_264])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:32:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.28  
% 2.18/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.28  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.18/1.28  
% 2.18/1.28  %Foreground sorts:
% 2.18/1.28  
% 2.18/1.28  
% 2.18/1.28  %Background operators:
% 2.18/1.28  
% 2.18/1.28  
% 2.18/1.28  %Foreground operators:
% 2.18/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.18/1.28  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.18/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.18/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.18/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.28  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.18/1.28  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.18/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.18/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.18/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.18/1.28  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.18/1.28  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.18/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.18/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.28  
% 2.18/1.30  tff(f_119, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.18/1.30  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.18/1.30  tff(f_68, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.18/1.30  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.18/1.30  tff(f_58, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.18/1.30  tff(f_91, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: (((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v3_pre_topc(B, A)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_tops_1)).
% 2.18/1.30  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.18/1.30  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.18/1.30  tff(f_74, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.18/1.30  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.18/1.30  tff(f_36, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.18/1.30  tff(f_54, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.18/1.30  tff(c_34, plain, (k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.18/1.30  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.18/1.30  tff(c_54, plain, (![A_2]: (r1_tarski('#skF_4', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_6])).
% 2.18/1.30  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.18/1.30  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.18/1.30  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.18/1.30  tff(c_22, plain, (![A_14]: (v4_pre_topc(k2_struct_0(A_14), A_14) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.18/1.30  tff(c_20, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.18/1.30  tff(c_80, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.18/1.30  tff(c_85, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_pre_topc(A_38))), inference(resolution, [status(thm)], [c_20, c_80])).
% 2.18/1.30  tff(c_89, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_85])).
% 2.18/1.30  tff(c_154, plain, (![A_53]: (m1_subset_1('#skF_1'(A_53), k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.18/1.30  tff(c_160, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_89, c_154])).
% 2.18/1.30  tff(c_163, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_160])).
% 2.18/1.30  tff(c_164, plain, (m1_subset_1('#skF_1'('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_44, c_163])).
% 2.18/1.30  tff(c_12, plain, (![B_7, A_5]: (v1_xboole_0(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.18/1.30  tff(c_180, plain, (v1_xboole_0('#skF_1'('#skF_2')) | ~v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_164, c_12])).
% 2.18/1.30  tff(c_181, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_180])).
% 2.18/1.30  tff(c_38, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.18/1.30  tff(c_101, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_38])).
% 2.18/1.30  tff(c_14, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.18/1.30  tff(c_24, plain, (![A_15]: (v3_pre_topc(k2_struct_0(A_15), A_15) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.18/1.30  tff(c_8, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.18/1.30  tff(c_10, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.18/1.30  tff(c_53, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 2.18/1.30  tff(c_52, plain, (![D_29]: (v3_pre_topc(D_29, '#skF_2') | ~r2_hidden(D_29, '#skF_4') | ~m1_subset_1(D_29, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.18/1.30  tff(c_112, plain, (![D_41]: (v3_pre_topc(D_41, '#skF_2') | ~r2_hidden(D_41, '#skF_4') | ~m1_subset_1(D_41, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_52])).
% 2.18/1.30  tff(c_117, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_53, c_112])).
% 2.18/1.30  tff(c_131, plain, (~r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(splitLeft, [status(thm)], [c_117])).
% 2.18/1.30  tff(c_46, plain, (![D_29]: (r2_hidden(D_29, '#skF_4') | ~r2_hidden('#skF_3', D_29) | ~v4_pre_topc(D_29, '#skF_2') | ~v3_pre_topc(D_29, '#skF_2') | ~m1_subset_1(D_29, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.18/1.30  tff(c_183, plain, (![D_54]: (r2_hidden(D_54, '#skF_4') | ~r2_hidden('#skF_3', D_54) | ~v4_pre_topc(D_54, '#skF_2') | ~v3_pre_topc(D_54, '#skF_2') | ~m1_subset_1(D_54, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_46])).
% 2.18/1.30  tff(c_190, plain, (r2_hidden(k2_struct_0('#skF_2'), '#skF_4') | ~r2_hidden('#skF_3', k2_struct_0('#skF_2')) | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_53, c_183])).
% 2.18/1.30  tff(c_194, plain, (~r2_hidden('#skF_3', k2_struct_0('#skF_2')) | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_131, c_190])).
% 2.18/1.30  tff(c_208, plain, (~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_194])).
% 2.18/1.30  tff(c_211, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_208])).
% 2.18/1.30  tff(c_215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_211])).
% 2.18/1.30  tff(c_216, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_194])).
% 2.18/1.30  tff(c_218, plain, (~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_216])).
% 2.18/1.30  tff(c_221, plain, (v1_xboole_0(k2_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_218])).
% 2.18/1.30  tff(c_224, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_221])).
% 2.18/1.30  tff(c_226, plain, $false, inference(negUnitSimplification, [status(thm)], [c_181, c_224])).
% 2.18/1.30  tff(c_227, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_216])).
% 2.18/1.30  tff(c_235, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_227])).
% 2.18/1.30  tff(c_239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_235])).
% 2.18/1.30  tff(c_240, plain, (v1_xboole_0('#skF_1'('#skF_2'))), inference(splitRight, [status(thm)], [c_180])).
% 2.18/1.30  tff(c_30, plain, (![A_16]: (~v1_xboole_0('#skF_1'(A_16)) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.18/1.30  tff(c_244, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_240, c_30])).
% 2.18/1.30  tff(c_250, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_244])).
% 2.18/1.30  tff(c_252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_250])).
% 2.18/1.30  tff(c_254, plain, (r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(splitRight, [status(thm)], [c_117])).
% 2.18/1.30  tff(c_16, plain, (![B_11, A_10]: (~r1_tarski(B_11, A_10) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.18/1.30  tff(c_264, plain, (~r1_tarski('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_254, c_16])).
% 2.18/1.30  tff(c_268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_264])).
% 2.18/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.30  
% 2.18/1.30  Inference rules
% 2.18/1.30  ----------------------
% 2.18/1.30  #Ref     : 0
% 2.18/1.30  #Sup     : 36
% 2.18/1.30  #Fact    : 0
% 2.18/1.30  #Define  : 0
% 2.18/1.30  #Split   : 5
% 2.18/1.30  #Chain   : 0
% 2.18/1.30  #Close   : 0
% 2.18/1.30  
% 2.18/1.30  Ordering : KBO
% 2.18/1.30  
% 2.18/1.30  Simplification rules
% 2.18/1.30  ----------------------
% 2.18/1.30  #Subsume      : 5
% 2.18/1.30  #Demod        : 28
% 2.18/1.30  #Tautology    : 13
% 2.18/1.30  #SimpNegUnit  : 5
% 2.18/1.30  #BackRed      : 2
% 2.18/1.30  
% 2.18/1.30  #Partial instantiations: 0
% 2.18/1.30  #Strategies tried      : 1
% 2.18/1.30  
% 2.18/1.30  Timing (in seconds)
% 2.18/1.30  ----------------------
% 2.18/1.30  Preprocessing        : 0.32
% 2.18/1.30  Parsing              : 0.17
% 2.18/1.30  CNF conversion       : 0.02
% 2.18/1.30  Main loop            : 0.20
% 2.18/1.30  Inferencing          : 0.08
% 2.18/1.30  Reduction            : 0.07
% 2.18/1.30  Demodulation         : 0.05
% 2.18/1.30  BG Simplification    : 0.01
% 2.18/1.30  Subsumption          : 0.03
% 2.18/1.30  Abstraction          : 0.01
% 2.18/1.30  MUC search           : 0.00
% 2.18/1.30  Cooper               : 0.00
% 2.18/1.30  Total                : 0.56
% 2.18/1.30  Index Insertion      : 0.00
% 2.18/1.30  Index Deletion       : 0.00
% 2.18/1.30  Index Matching       : 0.00
% 2.18/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
