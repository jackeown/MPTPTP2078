%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:56 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 133 expanded)
%              Number of leaves         :   40 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  131 ( 214 expanded)
%              Number of equality atoms :   38 (  72 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > v1_relat_1 > l1_orders_2 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k10_relat_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( r2_lattice3(A,k1_xboole_0,B)
              & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_79,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_52,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

tff(c_52,plain,
    ( ~ r1_lattice3('#skF_4',k1_xboole_0,'#skF_5')
    | ~ r2_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_91,plain,(
    ~ r2_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_56,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_251,plain,(
    ! [A_97,B_98,C_99] :
      ( r2_hidden('#skF_3'(A_97,B_98,C_99),B_98)
      | r2_lattice3(A_97,B_98,C_99)
      | ~ m1_subset_1(C_99,u1_struct_0(A_97))
      | ~ l1_orders_2(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_85,plain,(
    ! [A_55,B_56] : k2_xboole_0(k1_tarski(A_55),B_56) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_89,plain,(
    ! [A_55] : k1_tarski(A_55) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_85])).

tff(c_30,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_1'(A_18),A_18)
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( k4_xboole_0(k1_tarski(A_2),B_3) = k1_xboole_0
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_111,plain,(
    ! [B_67,A_68] :
      ( B_67 = A_68
      | k4_xboole_0(k1_tarski(A_68),k1_tarski(B_67)) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_117,plain,(
    ! [B_69,A_70] :
      ( B_69 = A_70
      | ~ r2_hidden(A_70,k1_tarski(B_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_111])).

tff(c_121,plain,(
    ! [B_69] :
      ( '#skF_1'(k1_tarski(B_69)) = B_69
      | k1_tarski(B_69) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_117])).

tff(c_124,plain,(
    ! [B_69] : '#skF_1'(k1_tarski(B_69)) = B_69 ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_121])).

tff(c_16,plain,(
    ! [A_11] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A_11))) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_154,plain,(
    ! [A_78,C_79,B_80] :
      ( m1_subset_1(A_78,C_79)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(C_79))
      | ~ r2_hidden(A_78,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_173,plain,(
    ! [A_86,A_87] :
      ( m1_subset_1(A_86,k1_zfmisc_1(A_87))
      | ~ r2_hidden(A_86,k1_tarski(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_16,c_154])).

tff(c_179,plain,(
    ! [A_87] :
      ( m1_subset_1('#skF_1'(k1_tarski(k1_xboole_0)),k1_zfmisc_1(A_87))
      | k1_tarski(k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_173])).

tff(c_182,plain,(
    ! [A_87] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_87))
      | k1_tarski(k1_xboole_0) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_179])).

tff(c_184,plain,(
    ! [A_88] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_88)) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_182])).

tff(c_28,plain,(
    ! [C_17,A_15,B_16] :
      ( v1_relat_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_194,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_184,c_28])).

tff(c_18,plain,(
    ! [A_12] : k10_relat_1(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_195,plain,(
    ! [B_89,A_90] :
      ( k10_relat_1(B_89,k1_tarski(A_90)) != k1_xboole_0
      | ~ r2_hidden(A_90,k2_relat_1(B_89))
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_202,plain,(
    ! [A_90] :
      ( k10_relat_1(k1_xboole_0,k1_tarski(A_90)) != k1_xboole_0
      | ~ r2_hidden(A_90,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_195])).

tff(c_205,plain,(
    ! [A_90] :
      ( ~ r2_hidden(A_90,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_202])).

tff(c_208,plain,(
    ! [A_90] : ~ r2_hidden(A_90,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_205])).

tff(c_282,plain,(
    ! [A_100,C_101] :
      ( r2_lattice3(A_100,k1_xboole_0,C_101)
      | ~ m1_subset_1(C_101,u1_struct_0(A_100))
      | ~ l1_orders_2(A_100) ) ),
    inference(resolution,[status(thm)],[c_251,c_208])).

tff(c_285,plain,
    ( r2_lattice3('#skF_4',k1_xboole_0,'#skF_5')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_282])).

tff(c_288,plain,(
    r2_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_285])).

tff(c_290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_288])).

tff(c_291,plain,(
    ~ r1_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_506,plain,(
    ! [A_149,B_150,C_151] :
      ( r2_hidden('#skF_2'(A_149,B_150,C_151),B_150)
      | r1_lattice3(A_149,B_150,C_151)
      | ~ m1_subset_1(C_151,u1_struct_0(A_149))
      | ~ l1_orders_2(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_312,plain,(
    ! [B_111,A_112] :
      ( B_111 = A_112
      | k4_xboole_0(k1_tarski(A_112),k1_tarski(B_111)) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_318,plain,(
    ! [B_113,A_114] :
      ( B_113 = A_114
      | ~ r2_hidden(A_114,k1_tarski(B_113)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_312])).

tff(c_322,plain,(
    ! [B_113] :
      ( '#skF_1'(k1_tarski(B_113)) = B_113
      | k1_tarski(B_113) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_318])).

tff(c_325,plain,(
    ! [B_113] : '#skF_1'(k1_tarski(B_113)) = B_113 ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_322])).

tff(c_355,plain,(
    ! [A_122,C_123,B_124] :
      ( m1_subset_1(A_122,C_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(C_123))
      | ~ r2_hidden(A_122,B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_364,plain,(
    ! [A_125,A_126] :
      ( m1_subset_1(A_125,k1_zfmisc_1(A_126))
      | ~ r2_hidden(A_125,k1_tarski(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_16,c_355])).

tff(c_370,plain,(
    ! [A_126] :
      ( m1_subset_1('#skF_1'(k1_tarski(k1_xboole_0)),k1_zfmisc_1(A_126))
      | k1_tarski(k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_364])).

tff(c_373,plain,(
    ! [A_126] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_126))
      | k1_tarski(k1_xboole_0) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_370])).

tff(c_375,plain,(
    ! [A_127] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_127)) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_373])).

tff(c_385,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_375,c_28])).

tff(c_433,plain,(
    ! [B_140,A_141] :
      ( k10_relat_1(B_140,k1_tarski(A_141)) != k1_xboole_0
      | ~ r2_hidden(A_141,k2_relat_1(B_140))
      | ~ v1_relat_1(B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_443,plain,(
    ! [A_141] :
      ( k10_relat_1(k1_xboole_0,k1_tarski(A_141)) != k1_xboole_0
      | ~ r2_hidden(A_141,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_433])).

tff(c_447,plain,(
    ! [A_141] : ~ r2_hidden(A_141,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_18,c_443])).

tff(c_538,plain,(
    ! [A_155,C_156] :
      ( r1_lattice3(A_155,k1_xboole_0,C_156)
      | ~ m1_subset_1(C_156,u1_struct_0(A_155))
      | ~ l1_orders_2(A_155) ) ),
    inference(resolution,[status(thm)],[c_506,c_447])).

tff(c_541,plain,
    ( r1_lattice3('#skF_4',k1_xboole_0,'#skF_5')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_538])).

tff(c_544,plain,(
    r1_lattice3('#skF_4',k1_xboole_0,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_541])).

tff(c_546,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_291,c_544])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:11:01 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.40  
% 2.83/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.40  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > v1_relat_1 > l1_orders_2 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k10_relat_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.83/1.40  
% 2.83/1.40  %Foreground sorts:
% 2.83/1.40  
% 2.83/1.40  
% 2.83/1.40  %Background operators:
% 2.83/1.40  
% 2.83/1.40  
% 2.83/1.40  %Foreground operators:
% 2.83/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.83/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.83/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.83/1.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.83/1.40  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.83/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.83/1.40  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 2.83/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.83/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.83/1.40  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 2.83/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.40  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.83/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.40  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.83/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.83/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.83/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.83/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.83/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.83/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.83/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.40  
% 2.83/1.42  tff(f_117, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_0)).
% 2.83/1.42  tff(f_107, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 2.83/1.42  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.83/1.42  tff(f_39, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.83/1.42  tff(f_79, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.83/1.42  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 2.83/1.42  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 2.83/1.42  tff(f_47, axiom, (![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_setfam_1)).
% 2.83/1.42  tff(f_45, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.83/1.42  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.83/1.42  tff(f_49, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.83/1.42  tff(f_52, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.83/1.42  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 2.83/1.42  tff(f_93, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattice3)).
% 2.83/1.42  tff(c_52, plain, (~r1_lattice3('#skF_4', k1_xboole_0, '#skF_5') | ~r2_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.83/1.42  tff(c_91, plain, (~r2_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(splitLeft, [status(thm)], [c_52])).
% 2.83/1.42  tff(c_56, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.83/1.42  tff(c_54, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.83/1.42  tff(c_251, plain, (![A_97, B_98, C_99]: (r2_hidden('#skF_3'(A_97, B_98, C_99), B_98) | r2_lattice3(A_97, B_98, C_99) | ~m1_subset_1(C_99, u1_struct_0(A_97)) | ~l1_orders_2(A_97))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.83/1.42  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.83/1.42  tff(c_85, plain, (![A_55, B_56]: (k2_xboole_0(k1_tarski(A_55), B_56)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.83/1.42  tff(c_89, plain, (![A_55]: (k1_tarski(A_55)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_85])).
% 2.83/1.42  tff(c_30, plain, (![A_18]: (r2_hidden('#skF_1'(A_18), A_18) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.83/1.42  tff(c_6, plain, (![A_2, B_3]: (k4_xboole_0(k1_tarski(A_2), B_3)=k1_xboole_0 | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.83/1.42  tff(c_111, plain, (![B_67, A_68]: (B_67=A_68 | k4_xboole_0(k1_tarski(A_68), k1_tarski(B_67))!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.83/1.42  tff(c_117, plain, (![B_69, A_70]: (B_69=A_70 | ~r2_hidden(A_70, k1_tarski(B_69)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_111])).
% 2.83/1.42  tff(c_121, plain, (![B_69]: ('#skF_1'(k1_tarski(B_69))=B_69 | k1_tarski(B_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_117])).
% 2.83/1.42  tff(c_124, plain, (![B_69]: ('#skF_1'(k1_tarski(B_69))=B_69)), inference(negUnitSimplification, [status(thm)], [c_89, c_121])).
% 2.83/1.42  tff(c_16, plain, (![A_11]: (m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A_11))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.83/1.42  tff(c_154, plain, (![A_78, C_79, B_80]: (m1_subset_1(A_78, C_79) | ~m1_subset_1(B_80, k1_zfmisc_1(C_79)) | ~r2_hidden(A_78, B_80))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.83/1.42  tff(c_173, plain, (![A_86, A_87]: (m1_subset_1(A_86, k1_zfmisc_1(A_87)) | ~r2_hidden(A_86, k1_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_16, c_154])).
% 2.83/1.42  tff(c_179, plain, (![A_87]: (m1_subset_1('#skF_1'(k1_tarski(k1_xboole_0)), k1_zfmisc_1(A_87)) | k1_tarski(k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_173])).
% 2.83/1.42  tff(c_182, plain, (![A_87]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_87)) | k1_tarski(k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_124, c_179])).
% 2.83/1.42  tff(c_184, plain, (![A_88]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_88)))), inference(negUnitSimplification, [status(thm)], [c_89, c_182])).
% 2.83/1.42  tff(c_28, plain, (![C_17, A_15, B_16]: (v1_relat_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.83/1.42  tff(c_194, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_184, c_28])).
% 2.83/1.42  tff(c_18, plain, (![A_12]: (k10_relat_1(k1_xboole_0, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.83/1.42  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.83/1.42  tff(c_195, plain, (![B_89, A_90]: (k10_relat_1(B_89, k1_tarski(A_90))!=k1_xboole_0 | ~r2_hidden(A_90, k2_relat_1(B_89)) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.83/1.42  tff(c_202, plain, (![A_90]: (k10_relat_1(k1_xboole_0, k1_tarski(A_90))!=k1_xboole_0 | ~r2_hidden(A_90, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_195])).
% 2.83/1.42  tff(c_205, plain, (![A_90]: (~r2_hidden(A_90, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_202])).
% 2.83/1.42  tff(c_208, plain, (![A_90]: (~r2_hidden(A_90, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_205])).
% 2.83/1.42  tff(c_282, plain, (![A_100, C_101]: (r2_lattice3(A_100, k1_xboole_0, C_101) | ~m1_subset_1(C_101, u1_struct_0(A_100)) | ~l1_orders_2(A_100))), inference(resolution, [status(thm)], [c_251, c_208])).
% 2.83/1.42  tff(c_285, plain, (r2_lattice3('#skF_4', k1_xboole_0, '#skF_5') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_54, c_282])).
% 2.83/1.42  tff(c_288, plain, (r2_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_285])).
% 2.83/1.42  tff(c_290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_288])).
% 2.83/1.42  tff(c_291, plain, (~r1_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(splitRight, [status(thm)], [c_52])).
% 2.83/1.42  tff(c_506, plain, (![A_149, B_150, C_151]: (r2_hidden('#skF_2'(A_149, B_150, C_151), B_150) | r1_lattice3(A_149, B_150, C_151) | ~m1_subset_1(C_151, u1_struct_0(A_149)) | ~l1_orders_2(A_149))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.83/1.42  tff(c_312, plain, (![B_111, A_112]: (B_111=A_112 | k4_xboole_0(k1_tarski(A_112), k1_tarski(B_111))!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.83/1.42  tff(c_318, plain, (![B_113, A_114]: (B_113=A_114 | ~r2_hidden(A_114, k1_tarski(B_113)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_312])).
% 2.83/1.42  tff(c_322, plain, (![B_113]: ('#skF_1'(k1_tarski(B_113))=B_113 | k1_tarski(B_113)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_318])).
% 2.83/1.42  tff(c_325, plain, (![B_113]: ('#skF_1'(k1_tarski(B_113))=B_113)), inference(negUnitSimplification, [status(thm)], [c_89, c_322])).
% 2.83/1.42  tff(c_355, plain, (![A_122, C_123, B_124]: (m1_subset_1(A_122, C_123) | ~m1_subset_1(B_124, k1_zfmisc_1(C_123)) | ~r2_hidden(A_122, B_124))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.83/1.42  tff(c_364, plain, (![A_125, A_126]: (m1_subset_1(A_125, k1_zfmisc_1(A_126)) | ~r2_hidden(A_125, k1_tarski(k1_xboole_0)))), inference(resolution, [status(thm)], [c_16, c_355])).
% 2.83/1.42  tff(c_370, plain, (![A_126]: (m1_subset_1('#skF_1'(k1_tarski(k1_xboole_0)), k1_zfmisc_1(A_126)) | k1_tarski(k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_364])).
% 2.83/1.42  tff(c_373, plain, (![A_126]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_126)) | k1_tarski(k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_325, c_370])).
% 2.83/1.42  tff(c_375, plain, (![A_127]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_127)))), inference(negUnitSimplification, [status(thm)], [c_89, c_373])).
% 2.83/1.42  tff(c_385, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_375, c_28])).
% 2.83/1.42  tff(c_433, plain, (![B_140, A_141]: (k10_relat_1(B_140, k1_tarski(A_141))!=k1_xboole_0 | ~r2_hidden(A_141, k2_relat_1(B_140)) | ~v1_relat_1(B_140))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.83/1.42  tff(c_443, plain, (![A_141]: (k10_relat_1(k1_xboole_0, k1_tarski(A_141))!=k1_xboole_0 | ~r2_hidden(A_141, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_433])).
% 2.83/1.42  tff(c_447, plain, (![A_141]: (~r2_hidden(A_141, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_385, c_18, c_443])).
% 2.83/1.42  tff(c_538, plain, (![A_155, C_156]: (r1_lattice3(A_155, k1_xboole_0, C_156) | ~m1_subset_1(C_156, u1_struct_0(A_155)) | ~l1_orders_2(A_155))), inference(resolution, [status(thm)], [c_506, c_447])).
% 2.83/1.42  tff(c_541, plain, (r1_lattice3('#skF_4', k1_xboole_0, '#skF_5') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_54, c_538])).
% 2.83/1.42  tff(c_544, plain, (r1_lattice3('#skF_4', k1_xboole_0, '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_541])).
% 2.83/1.42  tff(c_546, plain, $false, inference(negUnitSimplification, [status(thm)], [c_291, c_544])).
% 2.83/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.42  
% 2.83/1.42  Inference rules
% 2.83/1.42  ----------------------
% 2.83/1.42  #Ref     : 0
% 2.83/1.42  #Sup     : 102
% 2.83/1.42  #Fact    : 0
% 2.83/1.42  #Define  : 0
% 2.83/1.42  #Split   : 1
% 2.83/1.42  #Chain   : 0
% 2.83/1.42  #Close   : 0
% 2.83/1.42  
% 2.83/1.42  Ordering : KBO
% 2.83/1.42  
% 2.83/1.42  Simplification rules
% 2.83/1.42  ----------------------
% 2.83/1.42  #Subsume      : 8
% 2.83/1.42  #Demod        : 31
% 2.83/1.42  #Tautology    : 38
% 2.83/1.42  #SimpNegUnit  : 15
% 2.83/1.42  #BackRed      : 0
% 2.83/1.42  
% 2.83/1.42  #Partial instantiations: 0
% 2.83/1.42  #Strategies tried      : 1
% 2.83/1.42  
% 2.83/1.42  Timing (in seconds)
% 2.83/1.42  ----------------------
% 2.83/1.43  Preprocessing        : 0.35
% 2.83/1.43  Parsing              : 0.18
% 2.83/1.43  CNF conversion       : 0.03
% 2.83/1.43  Main loop            : 0.30
% 2.83/1.43  Inferencing          : 0.11
% 2.83/1.43  Reduction            : 0.09
% 2.83/1.43  Demodulation         : 0.05
% 2.83/1.43  BG Simplification    : 0.02
% 2.83/1.43  Subsumption          : 0.05
% 2.83/1.43  Abstraction          : 0.02
% 2.83/1.43  MUC search           : 0.00
% 2.83/1.43  Cooper               : 0.00
% 2.83/1.43  Total                : 0.69
% 2.83/1.43  Index Insertion      : 0.00
% 2.83/1.43  Index Deletion       : 0.00
% 2.83/1.43  Index Matching       : 0.00
% 2.83/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
