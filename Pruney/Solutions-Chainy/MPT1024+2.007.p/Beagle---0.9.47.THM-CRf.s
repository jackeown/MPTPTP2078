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
% DateTime   : Thu Dec  3 10:16:22 EST 2020

% Result     : Theorem 5.41s
% Output     : CNFRefutation 5.41s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 829 expanded)
%              Number of leaves         :   40 ( 305 expanded)
%              Depth                    :   12
%              Number of atoms          :  176 (2624 expanded)
%              Number of equality atoms :   49 ( 941 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_106,axiom,(
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

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_70,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_88,plain,(
    ! [C_86,A_87,B_88] :
      ( v1_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_97,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_70,c_88])).

tff(c_74,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_26,plain,(
    ! [A_18,B_41,D_56] :
      ( k1_funct_1(A_18,'#skF_5'(A_18,B_41,k9_relat_1(A_18,B_41),D_56)) = D_56
      | ~ r2_hidden(D_56,k9_relat_1(A_18,B_41))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    ! [A_18,B_41,D_56] :
      ( r2_hidden('#skF_5'(A_18,B_41,k9_relat_1(A_18,B_41),D_56),B_41)
      | ~ r2_hidden(D_56,k9_relat_1(A_18,B_41))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_72,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_153,plain,(
    ! [A_105,B_106,C_107] :
      ( k1_relset_1(A_105,B_106,C_107) = k1_relat_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_162,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_70,c_153])).

tff(c_340,plain,(
    ! [B_167,A_168,C_169] :
      ( k1_xboole_0 = B_167
      | k1_relset_1(A_168,B_167,C_169) = A_168
      | ~ v1_funct_2(C_169,A_168,B_167)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_168,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_347,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_340])).

tff(c_351,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_162,c_347])).

tff(c_352,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_351])).

tff(c_853,plain,(
    ! [A_259,B_260,D_261] :
      ( r2_hidden('#skF_5'(A_259,B_260,k9_relat_1(A_259,B_260),D_261),k1_relat_1(A_259))
      | ~ r2_hidden(D_261,k9_relat_1(A_259,B_260))
      | ~ v1_funct_1(A_259)
      | ~ v1_relat_1(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_865,plain,(
    ! [B_260,D_261] :
      ( r2_hidden('#skF_5'('#skF_9',B_260,k9_relat_1('#skF_9',B_260),D_261),'#skF_6')
      | ~ r2_hidden(D_261,k9_relat_1('#skF_9',B_260))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_853])).

tff(c_872,plain,(
    ! [B_262,D_263] :
      ( r2_hidden('#skF_5'('#skF_9',B_262,k9_relat_1('#skF_9',B_262),D_263),'#skF_6')
      | ~ r2_hidden(D_263,k9_relat_1('#skF_9',B_262)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_74,c_865])).

tff(c_66,plain,(
    ! [F_77] :
      ( k1_funct_1('#skF_9',F_77) != '#skF_10'
      | ~ r2_hidden(F_77,'#skF_8')
      | ~ r2_hidden(F_77,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_968,plain,(
    ! [B_281,D_282] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9',B_281,k9_relat_1('#skF_9',B_281),D_282)) != '#skF_10'
      | ~ r2_hidden('#skF_5'('#skF_9',B_281,k9_relat_1('#skF_9',B_281),D_282),'#skF_8')
      | ~ r2_hidden(D_282,k9_relat_1('#skF_9',B_281)) ) ),
    inference(resolution,[status(thm)],[c_872,c_66])).

tff(c_972,plain,(
    ! [D_56] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_56)) != '#skF_10'
      | ~ r2_hidden(D_56,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_28,c_968])).

tff(c_977,plain,(
    ! [D_285] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_285)) != '#skF_10'
      | ~ r2_hidden(D_285,k9_relat_1('#skF_9','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_74,c_972])).

tff(c_981,plain,(
    ! [D_56] :
      ( D_56 != '#skF_10'
      | ~ r2_hidden(D_56,k9_relat_1('#skF_9','#skF_8'))
      | ~ r2_hidden(D_56,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_977])).

tff(c_984,plain,(
    ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_74,c_981])).

tff(c_215,plain,(
    ! [A_127,B_128,C_129,D_130] :
      ( k7_relset_1(A_127,B_128,C_129,D_130) = k9_relat_1(C_129,D_130)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_222,plain,(
    ! [D_130] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_130) = k9_relat_1('#skF_9',D_130) ),
    inference(resolution,[status(thm)],[c_70,c_215])).

tff(c_68,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_228,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_68])).

tff(c_986,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_984,c_228])).

tff(c_988,plain,(
    k1_relat_1('#skF_9') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_351])).

tff(c_77,plain,(
    ! [A_81,B_82] :
      ( r1_tarski(A_81,B_82)
      | ~ m1_subset_1(A_81,k1_zfmisc_1(B_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_81,plain,(
    r1_tarski('#skF_9',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_70,c_77])).

tff(c_987,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_351])).

tff(c_8,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,k1_zfmisc_1(B_3))
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_261,plain,(
    ! [C_147,A_148] :
      ( k1_xboole_0 = C_147
      | ~ v1_funct_2(C_147,A_148,k1_xboole_0)
      | k1_xboole_0 = A_148
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_148,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_266,plain,(
    ! [A_2,A_148] :
      ( k1_xboole_0 = A_2
      | ~ v1_funct_2(A_2,A_148,k1_xboole_0)
      | k1_xboole_0 = A_148
      | ~ r1_tarski(A_2,k2_zfmisc_1(A_148,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_8,c_261])).

tff(c_2634,plain,(
    ! [A_473,A_474] :
      ( A_473 = '#skF_7'
      | ~ v1_funct_2(A_473,A_474,'#skF_7')
      | A_474 = '#skF_7'
      | ~ r1_tarski(A_473,k2_zfmisc_1(A_474,'#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_987,c_987,c_987,c_987,c_266])).

tff(c_2641,plain,
    ( '#skF_7' = '#skF_9'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_81,c_2634])).

tff(c_2646,plain,
    ( '#skF_7' = '#skF_9'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2641])).

tff(c_2647,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2646])).

tff(c_2673,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2647,c_72])).

tff(c_2669,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_9') = k1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2647,c_162])).

tff(c_2671,plain,(
    r1_tarski('#skF_9',k2_zfmisc_1('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2647,c_81])).

tff(c_274,plain,(
    ! [B_151,C_152] :
      ( k1_relset_1(k1_xboole_0,B_151,C_152) = k1_xboole_0
      | ~ v1_funct_2(C_152,k1_xboole_0,B_151)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_279,plain,(
    ! [B_151,A_2] :
      ( k1_relset_1(k1_xboole_0,B_151,A_2) = k1_xboole_0
      | ~ v1_funct_2(A_2,k1_xboole_0,B_151)
      | ~ r1_tarski(A_2,k2_zfmisc_1(k1_xboole_0,B_151)) ) ),
    inference(resolution,[status(thm)],[c_8,c_274])).

tff(c_994,plain,(
    ! [B_151,A_2] :
      ( k1_relset_1('#skF_7',B_151,A_2) = '#skF_7'
      | ~ v1_funct_2(A_2,'#skF_7',B_151)
      | ~ r1_tarski(A_2,k2_zfmisc_1('#skF_7',B_151)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_987,c_987,c_987,c_987,c_279])).

tff(c_3376,plain,(
    ! [B_538,A_539] :
      ( k1_relset_1('#skF_6',B_538,A_539) = '#skF_6'
      | ~ v1_funct_2(A_539,'#skF_6',B_538)
      | ~ r1_tarski(A_539,k2_zfmisc_1('#skF_6',B_538)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2647,c_2647,c_2647,c_2647,c_994])).

tff(c_3379,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_2671,c_3376])).

tff(c_3386,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2673,c_2669,c_3379])).

tff(c_3388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_988,c_3386])).

tff(c_3389,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_2646])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_98,plain,(
    ! [A_89,A_90,B_91] :
      ( v1_relat_1(A_89)
      | ~ r1_tarski(A_89,k2_zfmisc_1(A_90,B_91)) ) ),
    inference(resolution,[status(thm)],[c_8,c_88])).

tff(c_108,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_98])).

tff(c_309,plain,(
    ! [A_160,B_161,C_162] :
      ( r2_hidden(k4_tarski('#skF_1'(A_160,B_161,C_162),A_160),C_162)
      | ~ r2_hidden(A_160,k9_relat_1(C_162,B_161))
      | ~ v1_relat_1(C_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_132,plain,(
    ! [C_96,B_97,A_98] :
      ( ~ v1_xboole_0(C_96)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(C_96))
      | ~ r2_hidden(A_98,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_137,plain,(
    ! [B_3,A_98,A_2] :
      ( ~ v1_xboole_0(B_3)
      | ~ r2_hidden(A_98,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(resolution,[status(thm)],[c_8,c_132])).

tff(c_328,plain,(
    ! [B_163,C_164,A_165,B_166] :
      ( ~ v1_xboole_0(B_163)
      | ~ r1_tarski(C_164,B_163)
      | ~ r2_hidden(A_165,k9_relat_1(C_164,B_166))
      | ~ v1_relat_1(C_164) ) ),
    inference(resolution,[status(thm)],[c_309,c_137])).

tff(c_332,plain,(
    ! [A_1,A_165,B_166] :
      ( ~ v1_xboole_0(A_1)
      | ~ r2_hidden(A_165,k9_relat_1(k1_xboole_0,B_166))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_328])).

tff(c_338,plain,(
    ! [A_1,A_165,B_166] :
      ( ~ v1_xboole_0(A_1)
      | ~ r2_hidden(A_165,k9_relat_1(k1_xboole_0,B_166)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_332])).

tff(c_339,plain,(
    ! [A_165,B_166] : ~ r2_hidden(A_165,k9_relat_1(k1_xboole_0,B_166)) ),
    inference(splitLeft,[status(thm)],[c_338])).

tff(c_1598,plain,(
    ! [A_165,B_166] : ~ r2_hidden(A_165,k9_relat_1('#skF_7',B_166)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_987,c_339])).

tff(c_3403,plain,(
    ! [A_165,B_166] : ~ r2_hidden(A_165,k9_relat_1('#skF_9',B_166)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3389,c_1598])).

tff(c_3498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3403,c_228])).

tff(c_3499,plain,(
    ! [A_1] : ~ v1_xboole_0(A_1) ),
    inference(splitRight,[status(thm)],[c_338])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_3513,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3499,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:58:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.41/2.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.41/2.20  
% 5.41/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.41/2.21  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 5.41/2.21  
% 5.41/2.21  %Foreground sorts:
% 5.41/2.21  
% 5.41/2.21  
% 5.41/2.21  %Background operators:
% 5.41/2.21  
% 5.41/2.21  
% 5.41/2.21  %Foreground operators:
% 5.41/2.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.41/2.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.41/2.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.41/2.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.41/2.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.41/2.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.41/2.21  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.41/2.21  tff('#skF_7', type, '#skF_7': $i).
% 5.41/2.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.41/2.21  tff('#skF_10', type, '#skF_10': $i).
% 5.41/2.21  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.41/2.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.41/2.21  tff('#skF_6', type, '#skF_6': $i).
% 5.41/2.21  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.41/2.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.41/2.21  tff('#skF_9', type, '#skF_9': $i).
% 5.41/2.21  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.41/2.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.41/2.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.41/2.21  tff('#skF_8', type, '#skF_8': $i).
% 5.41/2.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.41/2.21  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 5.41/2.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.41/2.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.41/2.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.41/2.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.41/2.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.41/2.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.41/2.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.41/2.21  
% 5.41/2.22  tff(f_125, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 5.41/2.22  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.41/2.22  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 5.41/2.22  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.41/2.22  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.41/2.22  tff(f_88, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.41/2.22  tff(f_32, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.41/2.22  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.41/2.22  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 5.41/2.22  tff(f_39, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.41/2.22  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.41/2.22  tff(c_70, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.41/2.22  tff(c_88, plain, (![C_86, A_87, B_88]: (v1_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.41/2.22  tff(c_97, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_70, c_88])).
% 5.41/2.22  tff(c_74, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.41/2.22  tff(c_26, plain, (![A_18, B_41, D_56]: (k1_funct_1(A_18, '#skF_5'(A_18, B_41, k9_relat_1(A_18, B_41), D_56))=D_56 | ~r2_hidden(D_56, k9_relat_1(A_18, B_41)) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.41/2.22  tff(c_28, plain, (![A_18, B_41, D_56]: (r2_hidden('#skF_5'(A_18, B_41, k9_relat_1(A_18, B_41), D_56), B_41) | ~r2_hidden(D_56, k9_relat_1(A_18, B_41)) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.41/2.22  tff(c_72, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.41/2.22  tff(c_153, plain, (![A_105, B_106, C_107]: (k1_relset_1(A_105, B_106, C_107)=k1_relat_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.41/2.22  tff(c_162, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_70, c_153])).
% 5.41/2.22  tff(c_340, plain, (![B_167, A_168, C_169]: (k1_xboole_0=B_167 | k1_relset_1(A_168, B_167, C_169)=A_168 | ~v1_funct_2(C_169, A_168, B_167) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_168, B_167))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.41/2.22  tff(c_347, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_70, c_340])).
% 5.41/2.22  tff(c_351, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_162, c_347])).
% 5.41/2.22  tff(c_352, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_351])).
% 5.41/2.22  tff(c_853, plain, (![A_259, B_260, D_261]: (r2_hidden('#skF_5'(A_259, B_260, k9_relat_1(A_259, B_260), D_261), k1_relat_1(A_259)) | ~r2_hidden(D_261, k9_relat_1(A_259, B_260)) | ~v1_funct_1(A_259) | ~v1_relat_1(A_259))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.41/2.22  tff(c_865, plain, (![B_260, D_261]: (r2_hidden('#skF_5'('#skF_9', B_260, k9_relat_1('#skF_9', B_260), D_261), '#skF_6') | ~r2_hidden(D_261, k9_relat_1('#skF_9', B_260)) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_352, c_853])).
% 5.41/2.22  tff(c_872, plain, (![B_262, D_263]: (r2_hidden('#skF_5'('#skF_9', B_262, k9_relat_1('#skF_9', B_262), D_263), '#skF_6') | ~r2_hidden(D_263, k9_relat_1('#skF_9', B_262)))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_74, c_865])).
% 5.41/2.22  tff(c_66, plain, (![F_77]: (k1_funct_1('#skF_9', F_77)!='#skF_10' | ~r2_hidden(F_77, '#skF_8') | ~r2_hidden(F_77, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.41/2.22  tff(c_968, plain, (![B_281, D_282]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', B_281, k9_relat_1('#skF_9', B_281), D_282))!='#skF_10' | ~r2_hidden('#skF_5'('#skF_9', B_281, k9_relat_1('#skF_9', B_281), D_282), '#skF_8') | ~r2_hidden(D_282, k9_relat_1('#skF_9', B_281)))), inference(resolution, [status(thm)], [c_872, c_66])).
% 5.41/2.22  tff(c_972, plain, (![D_56]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_56))!='#skF_10' | ~r2_hidden(D_56, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_28, c_968])).
% 5.41/2.22  tff(c_977, plain, (![D_285]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_285))!='#skF_10' | ~r2_hidden(D_285, k9_relat_1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_74, c_972])).
% 5.41/2.22  tff(c_981, plain, (![D_56]: (D_56!='#skF_10' | ~r2_hidden(D_56, k9_relat_1('#skF_9', '#skF_8')) | ~r2_hidden(D_56, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_977])).
% 5.41/2.22  tff(c_984, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_74, c_981])).
% 5.41/2.22  tff(c_215, plain, (![A_127, B_128, C_129, D_130]: (k7_relset_1(A_127, B_128, C_129, D_130)=k9_relat_1(C_129, D_130) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.41/2.22  tff(c_222, plain, (![D_130]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_130)=k9_relat_1('#skF_9', D_130))), inference(resolution, [status(thm)], [c_70, c_215])).
% 5.41/2.22  tff(c_68, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.41/2.22  tff(c_228, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_68])).
% 5.41/2.22  tff(c_986, plain, $false, inference(negUnitSimplification, [status(thm)], [c_984, c_228])).
% 5.41/2.22  tff(c_988, plain, (k1_relat_1('#skF_9')!='#skF_6'), inference(splitRight, [status(thm)], [c_351])).
% 5.41/2.22  tff(c_77, plain, (![A_81, B_82]: (r1_tarski(A_81, B_82) | ~m1_subset_1(A_81, k1_zfmisc_1(B_82)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.41/2.22  tff(c_81, plain, (r1_tarski('#skF_9', k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_70, c_77])).
% 5.41/2.22  tff(c_987, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_351])).
% 5.41/2.22  tff(c_8, plain, (![A_2, B_3]: (m1_subset_1(A_2, k1_zfmisc_1(B_3)) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.41/2.22  tff(c_261, plain, (![C_147, A_148]: (k1_xboole_0=C_147 | ~v1_funct_2(C_147, A_148, k1_xboole_0) | k1_xboole_0=A_148 | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_148, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.41/2.22  tff(c_266, plain, (![A_2, A_148]: (k1_xboole_0=A_2 | ~v1_funct_2(A_2, A_148, k1_xboole_0) | k1_xboole_0=A_148 | ~r1_tarski(A_2, k2_zfmisc_1(A_148, k1_xboole_0)))), inference(resolution, [status(thm)], [c_8, c_261])).
% 5.41/2.22  tff(c_2634, plain, (![A_473, A_474]: (A_473='#skF_7' | ~v1_funct_2(A_473, A_474, '#skF_7') | A_474='#skF_7' | ~r1_tarski(A_473, k2_zfmisc_1(A_474, '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_987, c_987, c_987, c_987, c_266])).
% 5.41/2.22  tff(c_2641, plain, ('#skF_7'='#skF_9' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_81, c_2634])).
% 5.41/2.22  tff(c_2646, plain, ('#skF_7'='#skF_9' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2641])).
% 5.41/2.22  tff(c_2647, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_2646])).
% 5.41/2.22  tff(c_2673, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2647, c_72])).
% 5.41/2.22  tff(c_2669, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_9')=k1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2647, c_162])).
% 5.41/2.22  tff(c_2671, plain, (r1_tarski('#skF_9', k2_zfmisc_1('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2647, c_81])).
% 5.41/2.22  tff(c_274, plain, (![B_151, C_152]: (k1_relset_1(k1_xboole_0, B_151, C_152)=k1_xboole_0 | ~v1_funct_2(C_152, k1_xboole_0, B_151) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_151))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.41/2.22  tff(c_279, plain, (![B_151, A_2]: (k1_relset_1(k1_xboole_0, B_151, A_2)=k1_xboole_0 | ~v1_funct_2(A_2, k1_xboole_0, B_151) | ~r1_tarski(A_2, k2_zfmisc_1(k1_xboole_0, B_151)))), inference(resolution, [status(thm)], [c_8, c_274])).
% 5.41/2.22  tff(c_994, plain, (![B_151, A_2]: (k1_relset_1('#skF_7', B_151, A_2)='#skF_7' | ~v1_funct_2(A_2, '#skF_7', B_151) | ~r1_tarski(A_2, k2_zfmisc_1('#skF_7', B_151)))), inference(demodulation, [status(thm), theory('equality')], [c_987, c_987, c_987, c_987, c_279])).
% 5.41/2.22  tff(c_3376, plain, (![B_538, A_539]: (k1_relset_1('#skF_6', B_538, A_539)='#skF_6' | ~v1_funct_2(A_539, '#skF_6', B_538) | ~r1_tarski(A_539, k2_zfmisc_1('#skF_6', B_538)))), inference(demodulation, [status(thm), theory('equality')], [c_2647, c_2647, c_2647, c_2647, c_994])).
% 5.41/2.22  tff(c_3379, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_2671, c_3376])).
% 5.41/2.22  tff(c_3386, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2673, c_2669, c_3379])).
% 5.41/2.22  tff(c_3388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_988, c_3386])).
% 5.41/2.22  tff(c_3389, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_2646])).
% 5.41/2.22  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 5.41/2.22  tff(c_98, plain, (![A_89, A_90, B_91]: (v1_relat_1(A_89) | ~r1_tarski(A_89, k2_zfmisc_1(A_90, B_91)))), inference(resolution, [status(thm)], [c_8, c_88])).
% 5.41/2.22  tff(c_108, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_98])).
% 5.41/2.22  tff(c_309, plain, (![A_160, B_161, C_162]: (r2_hidden(k4_tarski('#skF_1'(A_160, B_161, C_162), A_160), C_162) | ~r2_hidden(A_160, k9_relat_1(C_162, B_161)) | ~v1_relat_1(C_162))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.41/2.22  tff(c_132, plain, (![C_96, B_97, A_98]: (~v1_xboole_0(C_96) | ~m1_subset_1(B_97, k1_zfmisc_1(C_96)) | ~r2_hidden(A_98, B_97))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.41/2.22  tff(c_137, plain, (![B_3, A_98, A_2]: (~v1_xboole_0(B_3) | ~r2_hidden(A_98, A_2) | ~r1_tarski(A_2, B_3))), inference(resolution, [status(thm)], [c_8, c_132])).
% 5.41/2.22  tff(c_328, plain, (![B_163, C_164, A_165, B_166]: (~v1_xboole_0(B_163) | ~r1_tarski(C_164, B_163) | ~r2_hidden(A_165, k9_relat_1(C_164, B_166)) | ~v1_relat_1(C_164))), inference(resolution, [status(thm)], [c_309, c_137])).
% 5.41/2.22  tff(c_332, plain, (![A_1, A_165, B_166]: (~v1_xboole_0(A_1) | ~r2_hidden(A_165, k9_relat_1(k1_xboole_0, B_166)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_328])).
% 5.41/2.22  tff(c_338, plain, (![A_1, A_165, B_166]: (~v1_xboole_0(A_1) | ~r2_hidden(A_165, k9_relat_1(k1_xboole_0, B_166)))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_332])).
% 5.41/2.22  tff(c_339, plain, (![A_165, B_166]: (~r2_hidden(A_165, k9_relat_1(k1_xboole_0, B_166)))), inference(splitLeft, [status(thm)], [c_338])).
% 5.41/2.22  tff(c_1598, plain, (![A_165, B_166]: (~r2_hidden(A_165, k9_relat_1('#skF_7', B_166)))), inference(demodulation, [status(thm), theory('equality')], [c_987, c_339])).
% 5.41/2.22  tff(c_3403, plain, (![A_165, B_166]: (~r2_hidden(A_165, k9_relat_1('#skF_9', B_166)))), inference(demodulation, [status(thm), theory('equality')], [c_3389, c_1598])).
% 5.41/2.22  tff(c_3498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3403, c_228])).
% 5.41/2.22  tff(c_3499, plain, (![A_1]: (~v1_xboole_0(A_1))), inference(splitRight, [status(thm)], [c_338])).
% 5.41/2.22  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.41/2.22  tff(c_3513, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3499, c_2])).
% 5.41/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.41/2.22  
% 5.41/2.22  Inference rules
% 5.41/2.22  ----------------------
% 5.41/2.22  #Ref     : 0
% 5.41/2.22  #Sup     : 664
% 5.41/2.22  #Fact    : 0
% 5.41/2.22  #Define  : 0
% 5.41/2.22  #Split   : 17
% 5.41/2.22  #Chain   : 0
% 5.41/2.22  #Close   : 0
% 5.41/2.22  
% 5.41/2.22  Ordering : KBO
% 5.41/2.22  
% 5.41/2.22  Simplification rules
% 5.41/2.22  ----------------------
% 5.41/2.22  #Subsume      : 132
% 5.41/2.22  #Demod        : 482
% 5.41/2.22  #Tautology    : 143
% 5.41/2.22  #SimpNegUnit  : 10
% 5.41/2.22  #BackRed      : 225
% 5.41/2.22  
% 5.41/2.22  #Partial instantiations: 0
% 5.41/2.22  #Strategies tried      : 1
% 5.41/2.22  
% 5.41/2.22  Timing (in seconds)
% 5.41/2.22  ----------------------
% 5.41/2.23  Preprocessing        : 0.51
% 5.41/2.23  Parsing              : 0.24
% 5.41/2.23  CNF conversion       : 0.04
% 5.41/2.23  Main loop            : 0.88
% 5.41/2.23  Inferencing          : 0.31
% 5.41/2.23  Reduction            : 0.25
% 5.41/2.23  Demodulation         : 0.17
% 5.41/2.23  BG Simplification    : 0.05
% 5.41/2.23  Subsumption          : 0.20
% 5.41/2.23  Abstraction          : 0.05
% 5.41/2.23  MUC search           : 0.00
% 5.41/2.23  Cooper               : 0.00
% 5.41/2.23  Total                : 1.43
% 5.41/2.23  Index Insertion      : 0.00
% 5.41/2.23  Index Deletion       : 0.00
% 5.41/2.23  Index Matching       : 0.00
% 5.41/2.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
