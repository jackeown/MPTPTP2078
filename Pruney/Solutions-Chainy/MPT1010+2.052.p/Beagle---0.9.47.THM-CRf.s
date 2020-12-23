%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:12 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 111 expanded)
%              Number of leaves         :   41 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  115 ( 208 expanded)
%              Number of equality atoms :   42 (  75 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_131,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_86,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_68,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_70,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_72,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_151,plain,(
    ! [C_71,A_72,B_73] :
      ( v1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_155,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_151])).

tff(c_76,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_74,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_284,plain,(
    ! [A_122,B_123,C_124] :
      ( k1_relset_1(A_122,B_123,C_124) = k1_relat_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_288,plain,(
    k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_284])).

tff(c_419,plain,(
    ! [B_151,A_152,C_153] :
      ( k1_xboole_0 = B_151
      | k1_relset_1(A_152,B_151,C_153) = A_152
      | ~ v1_funct_2(C_153,A_152,B_151)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_152,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_426,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_72,c_419])).

tff(c_430,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_288,c_426])).

tff(c_431,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_430])).

tff(c_260,plain,(
    ! [A_114,B_115,C_116] :
      ( k2_relset_1(A_114,B_115,C_116) = k2_relat_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_264,plain,(
    k2_relset_1('#skF_3',k1_tarski('#skF_4'),'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_260])).

tff(c_289,plain,(
    ! [A_125,B_126,C_127] :
      ( m1_subset_1(k2_relset_1(A_125,B_126,C_127),k1_zfmisc_1(B_126))
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_304,plain,
    ( m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1(k1_tarski('#skF_4')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_289])).

tff(c_309,plain,(
    m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1(k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_304])).

tff(c_321,plain,(
    ! [B_132,A_133] :
      ( r2_hidden(k1_funct_1(B_132,A_133),k2_relat_1(B_132))
      | ~ r2_hidden(A_133,k1_relat_1(B_132))
      | ~ v1_funct_1(B_132)
      | ~ v1_relat_1(B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    ! [C_18,A_15,B_16] :
      ( r2_hidden(C_18,A_15)
      | ~ r2_hidden(C_18,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_540,plain,(
    ! [B_180,A_181,A_182] :
      ( r2_hidden(k1_funct_1(B_180,A_181),A_182)
      | ~ m1_subset_1(k2_relat_1(B_180),k1_zfmisc_1(A_182))
      | ~ r2_hidden(A_181,k1_relat_1(B_180))
      | ~ v1_funct_1(B_180)
      | ~ v1_relat_1(B_180) ) ),
    inference(resolution,[status(thm)],[c_321,c_34])).

tff(c_542,plain,(
    ! [A_181] :
      ( r2_hidden(k1_funct_1('#skF_6',A_181),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_181,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_309,c_540])).

tff(c_546,plain,(
    ! [A_183] :
      ( r2_hidden(k1_funct_1('#skF_6',A_183),k1_tarski('#skF_4'))
      | ~ r2_hidden(A_183,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_76,c_431,c_542])).

tff(c_28,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_30,plain,(
    ! [A_10,B_11] : k1_enumset1(A_10,A_10,B_11) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_219,plain,(
    ! [E_99,C_100,B_101,A_102] :
      ( E_99 = C_100
      | E_99 = B_101
      | E_99 = A_102
      | ~ r2_hidden(E_99,k1_enumset1(A_102,B_101,C_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_246,plain,(
    ! [E_111,B_112,A_113] :
      ( E_111 = B_112
      | E_111 = A_113
      | E_111 = A_113
      | ~ r2_hidden(E_111,k2_tarski(A_113,B_112)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_219])).

tff(c_255,plain,(
    ! [E_111,A_9] :
      ( E_111 = A_9
      | E_111 = A_9
      | E_111 = A_9
      | ~ r2_hidden(E_111,k1_tarski(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_246])).

tff(c_558,plain,(
    ! [A_184] :
      ( k1_funct_1('#skF_6',A_184) = '#skF_4'
      | ~ r2_hidden(A_184,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_546,c_255])).

tff(c_572,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_70,c_558])).

tff(c_579,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_572])).

tff(c_580,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_430])).

tff(c_110,plain,(
    ! [A_65,B_66] : k1_enumset1(A_65,A_65,B_66) = k2_tarski(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [E_8,A_2,B_3] : r2_hidden(E_8,k1_enumset1(A_2,B_3,E_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_137,plain,(
    ! [B_67,A_68] : r2_hidden(B_67,k2_tarski(A_68,B_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_6])).

tff(c_145,plain,(
    ! [A_69] : r2_hidden(A_69,k1_tarski(A_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_137])).

tff(c_46,plain,(
    ! [B_27,A_26] :
      ( ~ r1_tarski(B_27,A_26)
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_149,plain,(
    ! [A_69] : ~ r1_tarski(k1_tarski(A_69),A_69) ),
    inference(resolution,[status(thm)],[c_145,c_46])).

tff(c_596,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_580,c_149])).

tff(c_604,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_596])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:26:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.43  
% 2.83/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.43  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.83/1.43  
% 2.83/1.43  %Foreground sorts:
% 2.83/1.43  
% 2.83/1.43  
% 2.83/1.43  %Background operators:
% 2.83/1.43  
% 2.83/1.43  
% 2.83/1.43  %Foreground operators:
% 2.83/1.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.83/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.83/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.83/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.83/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.83/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.83/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.83/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.83/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.83/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.83/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.83/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.83/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.83/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.83/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.83/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.83/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.83/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.83/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.43  
% 2.83/1.44  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.83/1.44  tff(f_131, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.83/1.44  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.83/1.44  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.83/1.44  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.83/1.44  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.83/1.44  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.83/1.44  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 2.83/1.44  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.83/1.44  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.83/1.44  tff(f_46, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.83/1.44  tff(f_42, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.83/1.44  tff(f_86, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.83/1.44  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.83/1.44  tff(c_68, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.83/1.44  tff(c_70, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.83/1.44  tff(c_72, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.83/1.44  tff(c_151, plain, (![C_71, A_72, B_73]: (v1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.83/1.44  tff(c_155, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_72, c_151])).
% 2.83/1.44  tff(c_76, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.83/1.44  tff(c_74, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.83/1.44  tff(c_284, plain, (![A_122, B_123, C_124]: (k1_relset_1(A_122, B_123, C_124)=k1_relat_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.83/1.44  tff(c_288, plain, (k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_72, c_284])).
% 2.83/1.44  tff(c_419, plain, (![B_151, A_152, C_153]: (k1_xboole_0=B_151 | k1_relset_1(A_152, B_151, C_153)=A_152 | ~v1_funct_2(C_153, A_152, B_151) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_152, B_151))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 2.83/1.44  tff(c_426, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_419])).
% 2.83/1.44  tff(c_430, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_288, c_426])).
% 2.83/1.44  tff(c_431, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_430])).
% 2.83/1.44  tff(c_260, plain, (![A_114, B_115, C_116]: (k2_relset_1(A_114, B_115, C_116)=k2_relat_1(C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.83/1.44  tff(c_264, plain, (k2_relset_1('#skF_3', k1_tarski('#skF_4'), '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_72, c_260])).
% 2.83/1.44  tff(c_289, plain, (![A_125, B_126, C_127]: (m1_subset_1(k2_relset_1(A_125, B_126, C_127), k1_zfmisc_1(B_126)) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.83/1.44  tff(c_304, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1(k1_tarski('#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_264, c_289])).
% 2.83/1.44  tff(c_309, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1(k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_304])).
% 2.83/1.44  tff(c_321, plain, (![B_132, A_133]: (r2_hidden(k1_funct_1(B_132, A_133), k2_relat_1(B_132)) | ~r2_hidden(A_133, k1_relat_1(B_132)) | ~v1_funct_1(B_132) | ~v1_relat_1(B_132))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.83/1.44  tff(c_34, plain, (![C_18, A_15, B_16]: (r2_hidden(C_18, A_15) | ~r2_hidden(C_18, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.83/1.44  tff(c_540, plain, (![B_180, A_181, A_182]: (r2_hidden(k1_funct_1(B_180, A_181), A_182) | ~m1_subset_1(k2_relat_1(B_180), k1_zfmisc_1(A_182)) | ~r2_hidden(A_181, k1_relat_1(B_180)) | ~v1_funct_1(B_180) | ~v1_relat_1(B_180))), inference(resolution, [status(thm)], [c_321, c_34])).
% 2.83/1.44  tff(c_542, plain, (![A_181]: (r2_hidden(k1_funct_1('#skF_6', A_181), k1_tarski('#skF_4')) | ~r2_hidden(A_181, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_309, c_540])).
% 2.83/1.44  tff(c_546, plain, (![A_183]: (r2_hidden(k1_funct_1('#skF_6', A_183), k1_tarski('#skF_4')) | ~r2_hidden(A_183, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_76, c_431, c_542])).
% 2.83/1.44  tff(c_28, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.83/1.44  tff(c_30, plain, (![A_10, B_11]: (k1_enumset1(A_10, A_10, B_11)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.83/1.44  tff(c_219, plain, (![E_99, C_100, B_101, A_102]: (E_99=C_100 | E_99=B_101 | E_99=A_102 | ~r2_hidden(E_99, k1_enumset1(A_102, B_101, C_100)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.83/1.44  tff(c_246, plain, (![E_111, B_112, A_113]: (E_111=B_112 | E_111=A_113 | E_111=A_113 | ~r2_hidden(E_111, k2_tarski(A_113, B_112)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_219])).
% 2.83/1.44  tff(c_255, plain, (![E_111, A_9]: (E_111=A_9 | E_111=A_9 | E_111=A_9 | ~r2_hidden(E_111, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_246])).
% 2.83/1.44  tff(c_558, plain, (![A_184]: (k1_funct_1('#skF_6', A_184)='#skF_4' | ~r2_hidden(A_184, '#skF_3'))), inference(resolution, [status(thm)], [c_546, c_255])).
% 2.83/1.44  tff(c_572, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_70, c_558])).
% 2.83/1.44  tff(c_579, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_572])).
% 2.83/1.44  tff(c_580, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_430])).
% 2.83/1.44  tff(c_110, plain, (![A_65, B_66]: (k1_enumset1(A_65, A_65, B_66)=k2_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.83/1.44  tff(c_6, plain, (![E_8, A_2, B_3]: (r2_hidden(E_8, k1_enumset1(A_2, B_3, E_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.83/1.44  tff(c_137, plain, (![B_67, A_68]: (r2_hidden(B_67, k2_tarski(A_68, B_67)))), inference(superposition, [status(thm), theory('equality')], [c_110, c_6])).
% 2.83/1.44  tff(c_145, plain, (![A_69]: (r2_hidden(A_69, k1_tarski(A_69)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_137])).
% 2.83/1.44  tff(c_46, plain, (![B_27, A_26]: (~r1_tarski(B_27, A_26) | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.83/1.44  tff(c_149, plain, (![A_69]: (~r1_tarski(k1_tarski(A_69), A_69))), inference(resolution, [status(thm)], [c_145, c_46])).
% 2.83/1.44  tff(c_596, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_580, c_149])).
% 2.83/1.44  tff(c_604, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_596])).
% 2.83/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.44  
% 2.83/1.44  Inference rules
% 2.83/1.44  ----------------------
% 2.83/1.44  #Ref     : 0
% 2.83/1.44  #Sup     : 115
% 2.83/1.44  #Fact    : 0
% 2.83/1.44  #Define  : 0
% 2.83/1.44  #Split   : 3
% 2.83/1.44  #Chain   : 0
% 2.83/1.44  #Close   : 0
% 2.83/1.44  
% 2.83/1.44  Ordering : KBO
% 2.83/1.44  
% 2.83/1.44  Simplification rules
% 2.83/1.44  ----------------------
% 2.83/1.44  #Subsume      : 14
% 2.83/1.44  #Demod        : 23
% 2.83/1.44  #Tautology    : 25
% 2.83/1.44  #SimpNegUnit  : 1
% 2.83/1.44  #BackRed      : 6
% 2.83/1.44  
% 2.83/1.44  #Partial instantiations: 0
% 2.83/1.44  #Strategies tried      : 1
% 2.83/1.44  
% 2.83/1.44  Timing (in seconds)
% 2.83/1.44  ----------------------
% 2.83/1.45  Preprocessing        : 0.35
% 2.83/1.45  Parsing              : 0.19
% 2.83/1.45  CNF conversion       : 0.02
% 2.83/1.45  Main loop            : 0.33
% 2.83/1.45  Inferencing          : 0.12
% 2.83/1.45  Reduction            : 0.10
% 2.83/1.45  Demodulation         : 0.07
% 2.83/1.45  BG Simplification    : 0.02
% 2.83/1.45  Subsumption          : 0.06
% 2.83/1.45  Abstraction          : 0.02
% 2.83/1.45  MUC search           : 0.00
% 2.83/1.45  Cooper               : 0.00
% 2.83/1.45  Total                : 0.71
% 2.83/1.45  Index Insertion      : 0.00
% 2.83/1.45  Index Deletion       : 0.00
% 2.83/1.45  Index Matching       : 0.00
% 2.83/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
