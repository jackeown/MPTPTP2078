%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:04 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 130 expanded)
%              Number of leaves         :   38 (  66 expanded)
%              Depth                    :   15
%              Number of atoms          :  147 ( 364 expanded)
%              Number of equality atoms :   17 (  41 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_133,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k4_orders_2(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_orders_2)).

tff(f_54,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_80,axiom,(
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

tff(f_115,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( m2_orders_2(C,A,B)
             => r2_hidden(k1_funct_1(B,u1_struct_0(A)),C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_orders_2)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_56,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_54,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_52,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_50,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_48,plain,(
    m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_106,plain,(
    ! [A_59] :
      ( v1_xboole_0(A_59)
      | r2_hidden('#skF_1'(A_59),A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_98,plain,(
    ! [A_56,B_57] : ~ r2_hidden(A_56,k2_zfmisc_1(A_56,B_57)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_104,plain,(
    ! [A_10] : ~ r2_hidden(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_98])).

tff(c_114,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_106,c_104])).

tff(c_348,plain,(
    ! [A_80,B_81] :
      ( ~ v1_xboole_0(k4_orders_2(A_80,B_81))
      | ~ m1_orders_1(B_81,k1_orders_1(u1_struct_0(A_80)))
      | ~ l1_orders_2(A_80)
      | ~ v5_orders_2(A_80)
      | ~ v4_orders_2(A_80)
      | ~ v3_orders_2(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_351,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_348])).

tff(c_354,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_351])).

tff(c_355,plain,(
    ~ v1_xboole_0(k4_orders_2('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_354])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_14] : k3_tarski(k1_tarski(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k1_tarski(A_8),B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_46,plain,(
    k3_tarski(k4_orders_2('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_164,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(k3_tarski(A_69),k3_tarski(B_70))
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_248,plain,(
    ! [A_76] :
      ( r1_tarski(k3_tarski(A_76),k1_xboole_0)
      | ~ r1_tarski(A_76,k4_orders_2('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_164])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_133,plain,(
    ! [B_66,A_67] :
      ( B_66 = A_67
      | ~ r1_tarski(B_66,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_145,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_133])).

tff(c_410,plain,(
    ! [A_84] :
      ( k3_tarski(A_84) = k1_xboole_0
      | ~ r1_tarski(A_84,k4_orders_2('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_248,c_145])).

tff(c_418,plain,(
    ! [A_8] :
      ( k3_tarski(k1_tarski(A_8)) = k1_xboole_0
      | ~ r2_hidden(A_8,k4_orders_2('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_16,c_410])).

tff(c_434,plain,(
    ! [A_85] :
      ( k1_xboole_0 = A_85
      | ~ r2_hidden(A_85,k4_orders_2('#skF_4','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_418])).

tff(c_438,plain,
    ( '#skF_1'(k4_orders_2('#skF_4','#skF_5')) = k1_xboole_0
    | v1_xboole_0(k4_orders_2('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_434])).

tff(c_441,plain,(
    '#skF_1'(k4_orders_2('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_355,c_438])).

tff(c_445,plain,
    ( v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
    | r2_hidden(k1_xboole_0,k4_orders_2('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_4])).

tff(c_448,plain,(
    r2_hidden(k1_xboole_0,k4_orders_2('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_355,c_445])).

tff(c_476,plain,(
    ! [D_89,A_90,B_91] :
      ( m2_orders_2(D_89,A_90,B_91)
      | ~ r2_hidden(D_89,k4_orders_2(A_90,B_91))
      | ~ m1_orders_1(B_91,k1_orders_1(u1_struct_0(A_90)))
      | ~ l1_orders_2(A_90)
      | ~ v5_orders_2(A_90)
      | ~ v4_orders_2(A_90)
      | ~ v3_orders_2(A_90)
      | v2_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_478,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_4','#skF_5')
    | ~ m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_448,c_476])).

tff(c_484,plain,
    ( m2_orders_2(k1_xboole_0,'#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_478])).

tff(c_485,plain,(
    m2_orders_2(k1_xboole_0,'#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_484])).

tff(c_774,plain,(
    ! [B_113,A_114,C_115] :
      ( r2_hidden(k1_funct_1(B_113,u1_struct_0(A_114)),C_115)
      | ~ m2_orders_2(C_115,A_114,B_113)
      | ~ m1_orders_1(B_113,k1_orders_1(u1_struct_0(A_114)))
      | ~ l1_orders_2(A_114)
      | ~ v5_orders_2(A_114)
      | ~ v4_orders_2(A_114)
      | ~ v3_orders_2(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2320,plain,(
    ! [C_188,A_189,B_190] :
      ( ~ v1_xboole_0(C_188)
      | ~ m2_orders_2(C_188,A_189,B_190)
      | ~ m1_orders_1(B_190,k1_orders_1(u1_struct_0(A_189)))
      | ~ l1_orders_2(A_189)
      | ~ v5_orders_2(A_189)
      | ~ v4_orders_2(A_189)
      | ~ v3_orders_2(A_189)
      | v2_struct_0(A_189) ) ),
    inference(resolution,[status(thm)],[c_774,c_2])).

tff(c_2328,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_485,c_2320])).

tff(c_2343,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_48,c_114,c_2328])).

tff(c_2345,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2343])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.09/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.70  
% 4.09/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.70  %$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 4.09/1.70  
% 4.09/1.70  %Foreground sorts:
% 4.09/1.70  
% 4.09/1.70  
% 4.09/1.70  %Background operators:
% 4.09/1.70  
% 4.09/1.70  
% 4.09/1.70  %Foreground operators:
% 4.09/1.70  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 4.09/1.70  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.09/1.70  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.09/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.09/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.09/1.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.09/1.70  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.09/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.09/1.70  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 4.09/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.09/1.70  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 4.09/1.70  tff('#skF_5', type, '#skF_5': $i).
% 4.09/1.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.09/1.70  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.09/1.70  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.09/1.70  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.09/1.70  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.09/1.70  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 4.09/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.09/1.70  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.09/1.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.09/1.70  tff('#skF_4', type, '#skF_4': $i).
% 4.09/1.70  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.09/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.09/1.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.09/1.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.09/1.70  
% 4.09/1.71  tff(f_133, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 4.09/1.71  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.09/1.71  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.09/1.71  tff(f_52, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 4.09/1.71  tff(f_96, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_orders_2)).
% 4.09/1.71  tff(f_54, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 4.09/1.71  tff(f_43, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.09/1.71  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 4.09/1.71  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.09/1.71  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.09/1.71  tff(f_80, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 4.09/1.71  tff(f_115, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_orders_2)).
% 4.09/1.71  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.09/1.71  tff(c_56, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.09/1.71  tff(c_54, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.09/1.71  tff(c_52, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.09/1.71  tff(c_50, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.09/1.71  tff(c_48, plain, (m1_orders_1('#skF_5', k1_orders_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.09/1.71  tff(c_106, plain, (![A_59]: (v1_xboole_0(A_59) | r2_hidden('#skF_1'(A_59), A_59))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.09/1.71  tff(c_20, plain, (![A_10]: (k2_zfmisc_1(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.09/1.71  tff(c_98, plain, (![A_56, B_57]: (~r2_hidden(A_56, k2_zfmisc_1(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.09/1.71  tff(c_104, plain, (![A_10]: (~r2_hidden(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_98])).
% 4.09/1.71  tff(c_114, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_106, c_104])).
% 4.09/1.71  tff(c_348, plain, (![A_80, B_81]: (~v1_xboole_0(k4_orders_2(A_80, B_81)) | ~m1_orders_1(B_81, k1_orders_1(u1_struct_0(A_80))) | ~l1_orders_2(A_80) | ~v5_orders_2(A_80) | ~v4_orders_2(A_80) | ~v3_orders_2(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.09/1.71  tff(c_351, plain, (~v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_348])).
% 4.09/1.71  tff(c_354, plain, (~v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_351])).
% 4.09/1.71  tff(c_355, plain, (~v1_xboole_0(k4_orders_2('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_58, c_354])).
% 4.09/1.71  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.09/1.71  tff(c_26, plain, (![A_14]: (k3_tarski(k1_tarski(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.09/1.71  tff(c_16, plain, (![A_8, B_9]: (r1_tarski(k1_tarski(A_8), B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.09/1.71  tff(c_46, plain, (k3_tarski(k4_orders_2('#skF_4', '#skF_5'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.09/1.71  tff(c_164, plain, (![A_69, B_70]: (r1_tarski(k3_tarski(A_69), k3_tarski(B_70)) | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.09/1.71  tff(c_248, plain, (![A_76]: (r1_tarski(k3_tarski(A_76), k1_xboole_0) | ~r1_tarski(A_76, k4_orders_2('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_46, c_164])).
% 4.09/1.71  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.09/1.71  tff(c_133, plain, (![B_66, A_67]: (B_66=A_67 | ~r1_tarski(B_66, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.09/1.71  tff(c_145, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_133])).
% 4.09/1.71  tff(c_410, plain, (![A_84]: (k3_tarski(A_84)=k1_xboole_0 | ~r1_tarski(A_84, k4_orders_2('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_248, c_145])).
% 4.09/1.71  tff(c_418, plain, (![A_8]: (k3_tarski(k1_tarski(A_8))=k1_xboole_0 | ~r2_hidden(A_8, k4_orders_2('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_16, c_410])).
% 4.09/1.71  tff(c_434, plain, (![A_85]: (k1_xboole_0=A_85 | ~r2_hidden(A_85, k4_orders_2('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_418])).
% 4.09/1.71  tff(c_438, plain, ('#skF_1'(k4_orders_2('#skF_4', '#skF_5'))=k1_xboole_0 | v1_xboole_0(k4_orders_2('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_4, c_434])).
% 4.09/1.71  tff(c_441, plain, ('#skF_1'(k4_orders_2('#skF_4', '#skF_5'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_355, c_438])).
% 4.09/1.71  tff(c_445, plain, (v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | r2_hidden(k1_xboole_0, k4_orders_2('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_441, c_4])).
% 4.09/1.71  tff(c_448, plain, (r2_hidden(k1_xboole_0, k4_orders_2('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_355, c_445])).
% 4.09/1.71  tff(c_476, plain, (![D_89, A_90, B_91]: (m2_orders_2(D_89, A_90, B_91) | ~r2_hidden(D_89, k4_orders_2(A_90, B_91)) | ~m1_orders_1(B_91, k1_orders_1(u1_struct_0(A_90))) | ~l1_orders_2(A_90) | ~v5_orders_2(A_90) | ~v4_orders_2(A_90) | ~v3_orders_2(A_90) | v2_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.09/1.71  tff(c_478, plain, (m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5') | ~m1_orders_1('#skF_5', k1_orders_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_448, c_476])).
% 4.09/1.71  tff(c_484, plain, (m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_478])).
% 4.09/1.71  tff(c_485, plain, (m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_58, c_484])).
% 4.09/1.71  tff(c_774, plain, (![B_113, A_114, C_115]: (r2_hidden(k1_funct_1(B_113, u1_struct_0(A_114)), C_115) | ~m2_orders_2(C_115, A_114, B_113) | ~m1_orders_1(B_113, k1_orders_1(u1_struct_0(A_114))) | ~l1_orders_2(A_114) | ~v5_orders_2(A_114) | ~v4_orders_2(A_114) | ~v3_orders_2(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.09/1.71  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.09/1.71  tff(c_2320, plain, (![C_188, A_189, B_190]: (~v1_xboole_0(C_188) | ~m2_orders_2(C_188, A_189, B_190) | ~m1_orders_1(B_190, k1_orders_1(u1_struct_0(A_189))) | ~l1_orders_2(A_189) | ~v5_orders_2(A_189) | ~v4_orders_2(A_189) | ~v3_orders_2(A_189) | v2_struct_0(A_189))), inference(resolution, [status(thm)], [c_774, c_2])).
% 4.09/1.71  tff(c_2328, plain, (~v1_xboole_0(k1_xboole_0) | ~m1_orders_1('#skF_5', k1_orders_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_485, c_2320])).
% 4.09/1.71  tff(c_2343, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_48, c_114, c_2328])).
% 4.09/1.71  tff(c_2345, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_2343])).
% 4.09/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.71  
% 4.09/1.71  Inference rules
% 4.09/1.71  ----------------------
% 4.09/1.71  #Ref     : 0
% 4.09/1.71  #Sup     : 476
% 4.09/1.71  #Fact    : 0
% 4.09/1.71  #Define  : 0
% 4.09/1.71  #Split   : 1
% 4.09/1.71  #Chain   : 0
% 4.09/1.71  #Close   : 0
% 4.09/1.71  
% 4.09/1.71  Ordering : KBO
% 4.09/1.71  
% 4.09/1.71  Simplification rules
% 4.09/1.71  ----------------------
% 4.09/1.71  #Subsume      : 75
% 4.09/1.71  #Demod        : 344
% 4.09/1.71  #Tautology    : 175
% 4.09/1.71  #SimpNegUnit  : 33
% 4.09/1.71  #BackRed      : 25
% 4.09/1.71  
% 4.09/1.71  #Partial instantiations: 0
% 4.09/1.71  #Strategies tried      : 1
% 4.09/1.71  
% 4.09/1.71  Timing (in seconds)
% 4.09/1.71  ----------------------
% 4.09/1.72  Preprocessing        : 0.31
% 4.09/1.72  Parsing              : 0.16
% 4.09/1.72  CNF conversion       : 0.03
% 4.09/1.72  Main loop            : 0.61
% 4.09/1.72  Inferencing          : 0.19
% 4.09/1.72  Reduction            : 0.20
% 4.09/1.72  Demodulation         : 0.14
% 4.09/1.72  BG Simplification    : 0.03
% 4.09/1.72  Subsumption          : 0.14
% 4.09/1.72  Abstraction          : 0.03
% 4.09/1.72  MUC search           : 0.00
% 4.09/1.72  Cooper               : 0.00
% 4.09/1.72  Total                : 0.95
% 4.09/1.72  Index Insertion      : 0.00
% 4.09/1.72  Index Deletion       : 0.00
% 4.09/1.72  Index Matching       : 0.00
% 4.09/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
