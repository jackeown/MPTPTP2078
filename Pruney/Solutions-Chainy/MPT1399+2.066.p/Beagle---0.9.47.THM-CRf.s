%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:27 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 241 expanded)
%              Number of leaves         :   33 (  93 expanded)
%              Depth                    :   12
%              Number of atoms          :  128 ( 630 expanded)
%              Number of equality atoms :   12 (  87 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_104,negated_conjecture,(
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

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_59,plain,(
    ! [A_28] :
      ( A_28 = '#skF_4'
      | ~ v1_xboole_0(A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2])).

tff(c_63,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4,c_59])).

tff(c_64,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_4])).

tff(c_32,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_30,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_20,plain,(
    ! [A_12] :
      ( v4_pre_topc(k2_struct_0(A_12),A_12)
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_16,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_75,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_80,plain,(
    ! [A_31] :
      ( u1_struct_0(A_31) = k2_struct_0(A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(resolution,[status(thm)],[c_16,c_75])).

tff(c_84,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_80])).

tff(c_18,plain,(
    ! [A_11] :
      ( ~ v1_xboole_0(u1_struct_0(A_11))
      | ~ l1_struct_0(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_91,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_18])).

tff(c_94,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_91])).

tff(c_96,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_106,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_96])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_106])).

tff(c_111,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_87,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_28])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_13] :
      ( v3_pre_topc(k2_struct_0(A_13),A_13)
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_2] : k2_subset_1(A_2) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k2_subset_1(A_3),k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_43,plain,(
    ! [A_3] : m1_subset_1(A_3,k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_38,plain,(
    ! [D_25] :
      ( r2_hidden('#skF_3',D_25)
      | ~ r2_hidden(D_25,'#skF_4')
      | ~ m1_subset_1(D_25,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_134,plain,(
    ! [D_43] :
      ( r2_hidden('#skF_3',D_43)
      | ~ r2_hidden(D_43,'#skF_4')
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_38])).

tff(c_139,plain,
    ( r2_hidden('#skF_3',k2_struct_0('#skF_2'))
    | ~ r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_43,c_134])).

tff(c_141,plain,(
    ~ r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_36,plain,(
    ! [D_25] :
      ( r2_hidden(D_25,'#skF_4')
      | ~ r2_hidden('#skF_3',D_25)
      | ~ v4_pre_topc(D_25,'#skF_2')
      | ~ v3_pre_topc(D_25,'#skF_2')
      | ~ m1_subset_1(D_25,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_162,plain,(
    ! [D_46] :
      ( r2_hidden(D_46,'#skF_4')
      | ~ r2_hidden('#skF_3',D_46)
      | ~ v4_pre_topc(D_46,'#skF_2')
      | ~ v3_pre_topc(D_46,'#skF_2')
      | ~ m1_subset_1(D_46,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_36])).

tff(c_166,plain,
    ( r2_hidden(k2_struct_0('#skF_2'),'#skF_4')
    | ~ r2_hidden('#skF_3',k2_struct_0('#skF_2'))
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_43,c_162])).

tff(c_169,plain,
    ( ~ r2_hidden('#skF_3',k2_struct_0('#skF_2'))
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_166])).

tff(c_170,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_173,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_170])).

tff(c_177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_173])).

tff(c_178,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_180,plain,(
    ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_183,plain,
    ( v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_180])).

tff(c_186,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_183])).

tff(c_188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_186])).

tff(c_189,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_197,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_189])).

tff(c_201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_197])).

tff(c_203,plain,(
    r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_121,plain,(
    ! [C_38,B_39,A_40] :
      ( ~ v1_xboole_0(C_38)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(C_38))
      | ~ r2_hidden(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_127,plain,(
    ! [A_3,A_40] :
      ( ~ v1_xboole_0(A_3)
      | ~ r2_hidden(A_40,A_3) ) ),
    inference(resolution,[status(thm)],[c_43,c_121])).

tff(c_217,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_203,c_127])).

tff(c_221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.30  % Computer   : n011.cluster.edu
% 0.12/0.30  % Model      : x86_64 x86_64
% 0.12/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.30  % Memory     : 8042.1875MB
% 0.12/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.30  % CPULimit   : 60
% 0.12/0.30  % DateTime   : Tue Dec  1 10:11:57 EST 2020
% 0.12/0.30  % CPUTime    : 
% 0.12/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.22  
% 2.13/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.22  %$ v4_pre_topc > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.13/1.22  
% 2.13/1.22  %Foreground sorts:
% 2.13/1.22  
% 2.13/1.22  
% 2.13/1.22  %Background operators:
% 2.13/1.22  
% 2.13/1.22  
% 2.13/1.22  %Foreground operators:
% 2.13/1.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.13/1.22  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.13/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.13/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.22  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.13/1.22  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.13/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.13/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.13/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.13/1.22  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.13/1.22  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.13/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.13/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.22  
% 2.24/1.24  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.24/1.24  tff(f_104, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.24/1.24  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.24/1.24  tff(f_70, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.24/1.24  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.24/1.24  tff(f_52, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.24/1.24  tff(f_64, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.24/1.24  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.24/1.24  tff(f_76, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.24/1.24  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.24/1.24  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.24/1.24  tff(f_48, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.24/1.24  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.24/1.24  tff(c_24, plain, (k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.24/1.24  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.24/1.24  tff(c_59, plain, (![A_28]: (A_28='#skF_4' | ~v1_xboole_0(A_28))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2])).
% 2.24/1.24  tff(c_63, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_4, c_59])).
% 2.24/1.24  tff(c_64, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_4])).
% 2.24/1.24  tff(c_32, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.24/1.24  tff(c_30, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.24/1.24  tff(c_20, plain, (![A_12]: (v4_pre_topc(k2_struct_0(A_12), A_12) | ~l1_pre_topc(A_12) | ~v2_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.24/1.24  tff(c_16, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.24/1.24  tff(c_34, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.24/1.24  tff(c_75, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.24/1.24  tff(c_80, plain, (![A_31]: (u1_struct_0(A_31)=k2_struct_0(A_31) | ~l1_pre_topc(A_31))), inference(resolution, [status(thm)], [c_16, c_75])).
% 2.24/1.24  tff(c_84, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_80])).
% 2.24/1.24  tff(c_18, plain, (![A_11]: (~v1_xboole_0(u1_struct_0(A_11)) | ~l1_struct_0(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.24/1.24  tff(c_91, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_84, c_18])).
% 2.24/1.24  tff(c_94, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_34, c_91])).
% 2.24/1.24  tff(c_96, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_94])).
% 2.24/1.24  tff(c_106, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_96])).
% 2.24/1.24  tff(c_110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_106])).
% 2.24/1.24  tff(c_111, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_94])).
% 2.24/1.24  tff(c_28, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.24/1.24  tff(c_87, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_28])).
% 2.24/1.24  tff(c_10, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.24/1.24  tff(c_22, plain, (![A_13]: (v3_pre_topc(k2_struct_0(A_13), A_13) | ~l1_pre_topc(A_13) | ~v2_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.24/1.24  tff(c_6, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.24/1.24  tff(c_8, plain, (![A_3]: (m1_subset_1(k2_subset_1(A_3), k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.24/1.24  tff(c_43, plain, (![A_3]: (m1_subset_1(A_3, k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 2.24/1.24  tff(c_38, plain, (![D_25]: (r2_hidden('#skF_3', D_25) | ~r2_hidden(D_25, '#skF_4') | ~m1_subset_1(D_25, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.24/1.24  tff(c_134, plain, (![D_43]: (r2_hidden('#skF_3', D_43) | ~r2_hidden(D_43, '#skF_4') | ~m1_subset_1(D_43, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_38])).
% 2.24/1.24  tff(c_139, plain, (r2_hidden('#skF_3', k2_struct_0('#skF_2')) | ~r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_43, c_134])).
% 2.24/1.24  tff(c_141, plain, (~r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(splitLeft, [status(thm)], [c_139])).
% 2.24/1.24  tff(c_36, plain, (![D_25]: (r2_hidden(D_25, '#skF_4') | ~r2_hidden('#skF_3', D_25) | ~v4_pre_topc(D_25, '#skF_2') | ~v3_pre_topc(D_25, '#skF_2') | ~m1_subset_1(D_25, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.24/1.24  tff(c_162, plain, (![D_46]: (r2_hidden(D_46, '#skF_4') | ~r2_hidden('#skF_3', D_46) | ~v4_pre_topc(D_46, '#skF_2') | ~v3_pre_topc(D_46, '#skF_2') | ~m1_subset_1(D_46, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_36])).
% 2.24/1.24  tff(c_166, plain, (r2_hidden(k2_struct_0('#skF_2'), '#skF_4') | ~r2_hidden('#skF_3', k2_struct_0('#skF_2')) | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_43, c_162])).
% 2.24/1.24  tff(c_169, plain, (~r2_hidden('#skF_3', k2_struct_0('#skF_2')) | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_141, c_166])).
% 2.24/1.24  tff(c_170, plain, (~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_169])).
% 2.24/1.24  tff(c_173, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_170])).
% 2.24/1.24  tff(c_177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_173])).
% 2.24/1.24  tff(c_178, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_169])).
% 2.24/1.24  tff(c_180, plain, (~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_178])).
% 2.24/1.24  tff(c_183, plain, (v1_xboole_0(k2_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_10, c_180])).
% 2.24/1.24  tff(c_186, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_183])).
% 2.24/1.24  tff(c_188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_186])).
% 2.24/1.24  tff(c_189, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_178])).
% 2.24/1.24  tff(c_197, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_189])).
% 2.24/1.24  tff(c_201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_197])).
% 2.24/1.24  tff(c_203, plain, (r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(splitRight, [status(thm)], [c_139])).
% 2.24/1.24  tff(c_121, plain, (![C_38, B_39, A_40]: (~v1_xboole_0(C_38) | ~m1_subset_1(B_39, k1_zfmisc_1(C_38)) | ~r2_hidden(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.24/1.24  tff(c_127, plain, (![A_3, A_40]: (~v1_xboole_0(A_3) | ~r2_hidden(A_40, A_3))), inference(resolution, [status(thm)], [c_43, c_121])).
% 2.24/1.24  tff(c_217, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_203, c_127])).
% 2.24/1.24  tff(c_221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_217])).
% 2.24/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.24  
% 2.24/1.24  Inference rules
% 2.24/1.24  ----------------------
% 2.24/1.24  #Ref     : 0
% 2.24/1.24  #Sup     : 31
% 2.24/1.24  #Fact    : 0
% 2.24/1.24  #Define  : 0
% 2.24/1.24  #Split   : 5
% 2.24/1.24  #Chain   : 0
% 2.24/1.24  #Close   : 0
% 2.24/1.24  
% 2.24/1.24  Ordering : KBO
% 2.24/1.24  
% 2.24/1.24  Simplification rules
% 2.24/1.24  ----------------------
% 2.24/1.24  #Subsume      : 4
% 2.24/1.24  #Demod        : 20
% 2.24/1.24  #Tautology    : 12
% 2.24/1.24  #SimpNegUnit  : 3
% 2.24/1.24  #BackRed      : 3
% 2.24/1.24  
% 2.24/1.24  #Partial instantiations: 0
% 2.24/1.24  #Strategies tried      : 1
% 2.24/1.24  
% 2.24/1.24  Timing (in seconds)
% 2.24/1.24  ----------------------
% 2.24/1.24  Preprocessing        : 0.32
% 2.24/1.24  Parsing              : 0.18
% 2.24/1.24  CNF conversion       : 0.02
% 2.24/1.24  Main loop            : 0.17
% 2.24/1.24  Inferencing          : 0.06
% 2.24/1.24  Reduction            : 0.06
% 2.24/1.24  Demodulation         : 0.04
% 2.24/1.24  BG Simplification    : 0.01
% 2.24/1.24  Subsumption          : 0.03
% 2.24/1.24  Abstraction          : 0.01
% 2.24/1.24  MUC search           : 0.00
% 2.24/1.24  Cooper               : 0.00
% 2.24/1.24  Total                : 0.53
% 2.24/1.24  Index Insertion      : 0.00
% 2.24/1.24  Index Deletion       : 0.00
% 2.24/1.24  Index Matching       : 0.00
% 2.24/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
