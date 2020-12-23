%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:02 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 301 expanded)
%              Number of leaves         :   41 ( 137 expanded)
%              Depth                    :   19
%              Number of atoms          :  177 (1037 expanded)
%              Number of equality atoms :   12 ( 110 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > v6_orders_2 > r2_wellord1 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k3_orders_2 > k4_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_wellord1,type,(
    r2_wellord1: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v6_orders_2,type,(
    v6_orders_2: ( $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => k3_tarski(k4_orders_2(A,B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).

tff(f_134,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k4_orders_2(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_orders_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( C = k4_orders_2(A,B)
            <=> ! [D] :
                  ( r2_hidden(D,C)
                <=> m2_orders_2(D,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ! [C] :
          ( m2_orders_2(C,A,B)
         => ( v6_orders_2(C,A)
            & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( ( v6_orders_2(C,A)
                & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
             => ( m2_orders_2(C,A,B)
              <=> ( C != k1_xboole_0
                  & r2_wellord1(u1_orders_2(A),C)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_hidden(D,C)
                       => k1_funct_1(B,k1_orders_2(A,k3_orders_2(A,C,D))) = D ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_orders_2)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_56,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_54,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_52,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_50,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_48,plain,(
    m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_108,plain,(
    ! [A_72,B_73] :
      ( ~ v1_xboole_0(k4_orders_2(A_72,B_73))
      | ~ m1_orders_1(B_73,k1_orders_1(u1_struct_0(A_72)))
      | ~ l1_orders_2(A_72)
      | ~ v5_orders_2(A_72)
      | ~ v4_orders_2(A_72)
      | ~ v3_orders_2(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_111,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_108])).

tff(c_114,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_111])).

tff(c_115,plain,(
    ~ v1_xboole_0(k4_orders_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_114])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_46,plain,(
    k3_tarski(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,k3_tarski(B_9))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_76,plain,(
    ! [B_68,A_69] :
      ( B_68 = A_69
      | ~ r1_tarski(B_68,A_69)
      | ~ r1_tarski(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_116,plain,(
    ! [B_74,A_75] :
      ( k3_tarski(B_74) = A_75
      | ~ r1_tarski(k3_tarski(B_74),A_75)
      | ~ r2_hidden(A_75,B_74) ) ),
    inference(resolution,[status(thm)],[c_14,c_76])).

tff(c_123,plain,(
    ! [A_75] :
      ( k3_tarski(k4_orders_2('#skF_5','#skF_6')) = A_75
      | ~ r1_tarski(k1_xboole_0,A_75)
      | ~ r2_hidden(A_75,k4_orders_2('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_116])).

tff(c_133,plain,(
    ! [A_76] :
      ( k1_xboole_0 = A_76
      | ~ r2_hidden(A_76,k4_orders_2('#skF_5','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_46,c_123])).

tff(c_137,plain,
    ( '#skF_1'(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0
    | v1_xboole_0(k4_orders_2('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_4,c_133])).

tff(c_140,plain,(
    '#skF_1'(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_137])).

tff(c_144,plain,
    ( v1_xboole_0(k4_orders_2('#skF_5','#skF_6'))
    | r2_hidden(k1_xboole_0,k4_orders_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_4])).

tff(c_147,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_144])).

tff(c_170,plain,(
    ! [D_82,A_83,B_84] :
      ( m2_orders_2(D_82,A_83,B_84)
      | ~ r2_hidden(D_82,k4_orders_2(A_83,B_84))
      | ~ m1_orders_1(B_84,k1_orders_1(u1_struct_0(A_83)))
      | ~ l1_orders_2(A_83)
      | ~ v5_orders_2(A_83)
      | ~ v4_orders_2(A_83)
      | ~ v3_orders_2(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_172,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_147,c_170])).

tff(c_178,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_172])).

tff(c_179,plain,(
    m2_orders_2(k1_xboole_0,'#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_178])).

tff(c_42,plain,(
    ! [C_57,A_54,B_55] :
      ( v6_orders_2(C_57,A_54)
      | ~ m2_orders_2(C_57,A_54,B_55)
      | ~ m1_orders_1(B_55,k1_orders_1(u1_struct_0(A_54)))
      | ~ l1_orders_2(A_54)
      | ~ v5_orders_2(A_54)
      | ~ v4_orders_2(A_54)
      | ~ v3_orders_2(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_185,plain,
    ( v6_orders_2(k1_xboole_0,'#skF_5')
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_179,c_42])).

tff(c_192,plain,
    ( v6_orders_2(k1_xboole_0,'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_185])).

tff(c_193,plain,(
    v6_orders_2(k1_xboole_0,'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_192])).

tff(c_40,plain,(
    ! [C_57,A_54,B_55] :
      ( m1_subset_1(C_57,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ m2_orders_2(C_57,A_54,B_55)
      | ~ m1_orders_1(B_55,k1_orders_1(u1_struct_0(A_54)))
      | ~ l1_orders_2(A_54)
      | ~ v5_orders_2(A_54)
      | ~ v4_orders_2(A_54)
      | ~ v3_orders_2(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_183,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_179,c_40])).

tff(c_188,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_183])).

tff(c_189,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_188])).

tff(c_266,plain,(
    ! [A_96,B_97] :
      ( ~ m2_orders_2(k1_xboole_0,A_96,B_97)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ v6_orders_2(k1_xboole_0,A_96)
      | ~ m1_orders_1(B_97,k1_orders_1(u1_struct_0(A_96)))
      | ~ l1_orders_2(A_96)
      | ~ v5_orders_2(A_96)
      | ~ v4_orders_2(A_96)
      | ~ v3_orders_2(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_268,plain,(
    ! [B_97] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_5',B_97)
      | ~ v6_orders_2(k1_xboole_0,'#skF_5')
      | ~ m1_orders_1(B_97,k1_orders_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_189,c_266])).

tff(c_271,plain,(
    ! [B_97] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_5',B_97)
      | ~ m1_orders_1(B_97,k1_orders_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_193,c_268])).

tff(c_273,plain,(
    ! [B_98] :
      ( ~ m2_orders_2(k1_xboole_0,'#skF_5',B_98)
      | ~ m1_orders_1(B_98,k1_orders_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_271])).

tff(c_276,plain,(
    ~ m2_orders_2(k1_xboole_0,'#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_273])).

tff(c_280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_276])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:16:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.40  
% 2.41/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.41  %$ m2_orders_2 > v6_orders_2 > r2_wellord1 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k3_orders_2 > k4_orders_2 > k1_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > u1_orders_2 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.41/1.41  
% 2.41/1.41  %Foreground sorts:
% 2.41/1.41  
% 2.41/1.41  
% 2.41/1.41  %Background operators:
% 2.41/1.41  
% 2.41/1.41  
% 2.41/1.41  %Foreground operators:
% 2.41/1.41  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.41/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.41/1.41  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.41/1.41  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 2.41/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.41/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.41/1.41  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 2.41/1.41  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.41/1.41  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.41/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.41/1.41  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.41/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.41/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.41/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.41/1.41  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.41/1.41  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.41/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.41/1.41  tff(r2_wellord1, type, r2_wellord1: ($i * $i) > $o).
% 2.41/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.41/1.41  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.41/1.41  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.41/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.41/1.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.41/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.41  tff(v6_orders_2, type, v6_orders_2: ($i * $i) > $o).
% 2.41/1.41  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.41/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.41/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.41/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.41/1.41  
% 2.41/1.42  tff(f_152, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 2.41/1.42  tff(f_134, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_orders_2)).
% 2.41/1.42  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.41/1.42  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.41/1.42  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.41/1.42  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.41/1.42  tff(f_98, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 2.41/1.42  tff(f_118, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (![C]: (m2_orders_2(C, A, B) => (v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.41/1.42  tff(f_76, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((v6_orders_2(C, A) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => (m2_orders_2(C, A, B) <=> ((~(C = k1_xboole_0) & r2_wellord1(u1_orders_2(A), C)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => (k1_funct_1(B, k1_orders_2(A, k3_orders_2(A, C, D))) = D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_orders_2)).
% 2.41/1.42  tff(c_58, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.41/1.42  tff(c_56, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.41/1.42  tff(c_54, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.41/1.42  tff(c_52, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.41/1.42  tff(c_50, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.41/1.42  tff(c_48, plain, (m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.41/1.42  tff(c_108, plain, (![A_72, B_73]: (~v1_xboole_0(k4_orders_2(A_72, B_73)) | ~m1_orders_1(B_73, k1_orders_1(u1_struct_0(A_72))) | ~l1_orders_2(A_72) | ~v5_orders_2(A_72) | ~v4_orders_2(A_72) | ~v3_orders_2(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.41/1.42  tff(c_111, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_48, c_108])).
% 2.41/1.42  tff(c_114, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_111])).
% 2.41/1.42  tff(c_115, plain, (~v1_xboole_0(k4_orders_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_58, c_114])).
% 2.41/1.42  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.41/1.42  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.41/1.42  tff(c_46, plain, (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_152])).
% 2.41/1.42  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, k3_tarski(B_9)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.41/1.42  tff(c_76, plain, (![B_68, A_69]: (B_68=A_69 | ~r1_tarski(B_68, A_69) | ~r1_tarski(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.41/1.42  tff(c_116, plain, (![B_74, A_75]: (k3_tarski(B_74)=A_75 | ~r1_tarski(k3_tarski(B_74), A_75) | ~r2_hidden(A_75, B_74))), inference(resolution, [status(thm)], [c_14, c_76])).
% 2.41/1.42  tff(c_123, plain, (![A_75]: (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))=A_75 | ~r1_tarski(k1_xboole_0, A_75) | ~r2_hidden(A_75, k4_orders_2('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_46, c_116])).
% 2.41/1.42  tff(c_133, plain, (![A_76]: (k1_xboole_0=A_76 | ~r2_hidden(A_76, k4_orders_2('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_46, c_123])).
% 2.41/1.42  tff(c_137, plain, ('#skF_1'(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0 | v1_xboole_0(k4_orders_2('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_4, c_133])).
% 2.41/1.42  tff(c_140, plain, ('#skF_1'(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_115, c_137])).
% 2.41/1.42  tff(c_144, plain, (v1_xboole_0(k4_orders_2('#skF_5', '#skF_6')) | r2_hidden(k1_xboole_0, k4_orders_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_140, c_4])).
% 2.41/1.42  tff(c_147, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_115, c_144])).
% 2.41/1.42  tff(c_170, plain, (![D_82, A_83, B_84]: (m2_orders_2(D_82, A_83, B_84) | ~r2_hidden(D_82, k4_orders_2(A_83, B_84)) | ~m1_orders_1(B_84, k1_orders_1(u1_struct_0(A_83))) | ~l1_orders_2(A_83) | ~v5_orders_2(A_83) | ~v4_orders_2(A_83) | ~v3_orders_2(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.41/1.42  tff(c_172, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_147, c_170])).
% 2.41/1.42  tff(c_178, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_172])).
% 2.41/1.42  tff(c_179, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_58, c_178])).
% 2.41/1.42  tff(c_42, plain, (![C_57, A_54, B_55]: (v6_orders_2(C_57, A_54) | ~m2_orders_2(C_57, A_54, B_55) | ~m1_orders_1(B_55, k1_orders_1(u1_struct_0(A_54))) | ~l1_orders_2(A_54) | ~v5_orders_2(A_54) | ~v4_orders_2(A_54) | ~v3_orders_2(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.41/1.42  tff(c_185, plain, (v6_orders_2(k1_xboole_0, '#skF_5') | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_179, c_42])).
% 2.41/1.42  tff(c_192, plain, (v6_orders_2(k1_xboole_0, '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_185])).
% 2.41/1.42  tff(c_193, plain, (v6_orders_2(k1_xboole_0, '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_192])).
% 2.41/1.42  tff(c_40, plain, (![C_57, A_54, B_55]: (m1_subset_1(C_57, k1_zfmisc_1(u1_struct_0(A_54))) | ~m2_orders_2(C_57, A_54, B_55) | ~m1_orders_1(B_55, k1_orders_1(u1_struct_0(A_54))) | ~l1_orders_2(A_54) | ~v5_orders_2(A_54) | ~v4_orders_2(A_54) | ~v3_orders_2(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.41/1.42  tff(c_183, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_179, c_40])).
% 2.41/1.42  tff(c_188, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_183])).
% 2.41/1.42  tff(c_189, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_188])).
% 2.41/1.42  tff(c_266, plain, (![A_96, B_97]: (~m2_orders_2(k1_xboole_0, A_96, B_97) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_96))) | ~v6_orders_2(k1_xboole_0, A_96) | ~m1_orders_1(B_97, k1_orders_1(u1_struct_0(A_96))) | ~l1_orders_2(A_96) | ~v5_orders_2(A_96) | ~v4_orders_2(A_96) | ~v3_orders_2(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.41/1.42  tff(c_268, plain, (![B_97]: (~m2_orders_2(k1_xboole_0, '#skF_5', B_97) | ~v6_orders_2(k1_xboole_0, '#skF_5') | ~m1_orders_1(B_97, k1_orders_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_189, c_266])).
% 2.41/1.42  tff(c_271, plain, (![B_97]: (~m2_orders_2(k1_xboole_0, '#skF_5', B_97) | ~m1_orders_1(B_97, k1_orders_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_193, c_268])).
% 2.41/1.42  tff(c_273, plain, (![B_98]: (~m2_orders_2(k1_xboole_0, '#skF_5', B_98) | ~m1_orders_1(B_98, k1_orders_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_271])).
% 2.41/1.42  tff(c_276, plain, (~m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_48, c_273])).
% 2.41/1.42  tff(c_280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179, c_276])).
% 2.41/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.42  
% 2.41/1.42  Inference rules
% 2.41/1.42  ----------------------
% 2.41/1.42  #Ref     : 0
% 2.41/1.42  #Sup     : 41
% 2.41/1.42  #Fact    : 0
% 2.41/1.42  #Define  : 0
% 2.41/1.42  #Split   : 0
% 2.41/1.42  #Chain   : 0
% 2.41/1.42  #Close   : 0
% 2.41/1.42  
% 2.41/1.42  Ordering : KBO
% 2.41/1.42  
% 2.41/1.42  Simplification rules
% 2.41/1.42  ----------------------
% 2.41/1.42  #Subsume      : 4
% 2.41/1.42  #Demod        : 64
% 2.41/1.42  #Tautology    : 19
% 2.41/1.42  #SimpNegUnit  : 13
% 2.41/1.42  #BackRed      : 0
% 2.41/1.42  
% 2.41/1.42  #Partial instantiations: 0
% 2.41/1.42  #Strategies tried      : 1
% 2.41/1.42  
% 2.41/1.42  Timing (in seconds)
% 2.41/1.42  ----------------------
% 2.41/1.42  Preprocessing        : 0.39
% 2.41/1.43  Parsing              : 0.21
% 2.41/1.43  CNF conversion       : 0.03
% 2.41/1.43  Main loop            : 0.21
% 2.41/1.43  Inferencing          : 0.07
% 2.41/1.43  Reduction            : 0.07
% 2.41/1.43  Demodulation         : 0.05
% 2.41/1.43  BG Simplification    : 0.02
% 2.41/1.43  Subsumption          : 0.04
% 2.41/1.43  Abstraction          : 0.01
% 2.41/1.43  MUC search           : 0.00
% 2.41/1.43  Cooper               : 0.00
% 2.41/1.43  Total                : 0.64
% 2.41/1.43  Index Insertion      : 0.00
% 2.41/1.43  Index Deletion       : 0.00
% 2.41/1.43  Index Matching       : 0.00
% 2.41/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
