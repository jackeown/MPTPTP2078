%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:34 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 124 expanded)
%              Number of leaves         :   36 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :  132 ( 305 expanded)
%              Number of equality atoms :   34 (  66 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > o_1_0_wellord2 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(o_1_0_wellord2,type,(
    o_1_0_wellord2: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,A)
                   => k7_partfun1(B,C,D) = k3_funct_2(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_72,axiom,(
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

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(o_1_0_wellord2(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_1_0_wellord2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_36,plain,(
    m1_subset_1('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_71,plain,(
    ! [C_51,B_52,A_53] :
      ( v5_relat_1(C_51,B_52)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_53,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_79,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_71])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_55,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_63,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_55])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_40,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_102,plain,(
    ! [A_63,B_64,C_65] :
      ( k1_relset_1(A_63,B_64,C_65) = k1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_110,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_102])).

tff(c_170,plain,(
    ! [B_80,A_81,C_82] :
      ( k1_xboole_0 = B_80
      | k1_relset_1(A_81,B_80,C_82) = A_81
      | ~ v1_funct_2(C_82,A_81,B_80)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_81,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_173,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_170])).

tff(c_180,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_110,c_173])).

tff(c_183,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_193,plain,(
    ! [A_83,B_84,C_85] :
      ( k7_partfun1(A_83,B_84,C_85) = k1_funct_1(B_84,C_85)
      | ~ r2_hidden(C_85,k1_relat_1(B_84))
      | ~ v1_funct_1(B_84)
      | ~ v5_relat_1(B_84,A_83)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_195,plain,(
    ! [A_83,C_85] :
      ( k7_partfun1(A_83,'#skF_3',C_85) = k1_funct_1('#skF_3',C_85)
      | ~ r2_hidden(C_85,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_83)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_193])).

tff(c_202,plain,(
    ! [A_86,C_87] :
      ( k7_partfun1(A_86,'#skF_3',C_87) = k1_funct_1('#skF_3',C_87)
      | ~ r2_hidden(C_87,'#skF_1')
      | ~ v5_relat_1('#skF_3',A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_42,c_195])).

tff(c_205,plain,(
    ! [A_86,A_2] :
      ( k7_partfun1(A_86,'#skF_3',A_2) = k1_funct_1('#skF_3',A_2)
      | ~ v5_relat_1('#skF_3',A_86)
      | v1_xboole_0('#skF_1')
      | ~ m1_subset_1(A_2,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_4,c_202])).

tff(c_209,plain,(
    ! [A_88,A_89] :
      ( k7_partfun1(A_88,'#skF_3',A_89) = k1_funct_1('#skF_3',A_89)
      | ~ v5_relat_1('#skF_3',A_88)
      | ~ m1_subset_1(A_89,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_205])).

tff(c_213,plain,(
    ! [A_90] :
      ( k7_partfun1('#skF_2','#skF_3',A_90) = k1_funct_1('#skF_3',A_90)
      | ~ m1_subset_1(A_90,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_79,c_209])).

tff(c_222,plain,(
    k7_partfun1('#skF_2','#skF_3','#skF_4') = k1_funct_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_213])).

tff(c_34,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') != k7_partfun1('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_223,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') != k1_funct_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_34])).

tff(c_228,plain,(
    ! [A_91,B_92,C_93,D_94] :
      ( k3_funct_2(A_91,B_92,C_93,D_94) = k1_funct_1(C_93,D_94)
      | ~ m1_subset_1(D_94,A_91)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ v1_funct_2(C_93,A_91,B_92)
      | ~ v1_funct_1(C_93)
      | v1_xboole_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_234,plain,(
    ! [B_92,C_93] :
      ( k3_funct_2('#skF_1',B_92,C_93,'#skF_4') = k1_funct_1(C_93,'#skF_4')
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_92)))
      | ~ v1_funct_2(C_93,'#skF_1',B_92)
      | ~ v1_funct_1(C_93)
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_228])).

tff(c_265,plain,(
    ! [B_99,C_100] :
      ( k3_funct_2('#skF_1',B_99,C_100,'#skF_4') = k1_funct_1(C_100,'#skF_4')
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_99)))
      | ~ v1_funct_2(C_100,'#skF_1',B_99)
      | ~ v1_funct_1(C_100) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_234])).

tff(c_268,plain,
    ( k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') = k1_funct_1('#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_265])).

tff(c_275,plain,(
    k3_funct_2('#skF_1','#skF_2','#skF_3','#skF_4') = k1_funct_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_268])).

tff(c_277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_223,c_275])).

tff(c_278,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_16,plain,(
    ! [A_15] : m1_subset_1(o_1_0_wellord2(A_15),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_50,plain,(
    ! [A_42,B_43] :
      ( r2_hidden(A_42,B_43)
      | v1_xboole_0(B_43)
      | ~ m1_subset_1(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( ~ r1_tarski(B_5,A_4)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_66,plain,(
    ! [B_49,A_50] :
      ( ~ r1_tarski(B_49,A_50)
      | v1_xboole_0(B_49)
      | ~ m1_subset_1(A_50,B_49) ) ),
    inference(resolution,[status(thm)],[c_50,c_6])).

tff(c_70,plain,(
    ! [A_1] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_1,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_66])).

tff(c_82,plain,(
    ! [A_54] : ~ m1_subset_1(A_54,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_87,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_16,c_82])).

tff(c_88,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_289,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_88])).

tff(c_292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_289])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:36:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.32  
% 2.46/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.32  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > o_1_0_wellord2 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.46/1.32  
% 2.46/1.32  %Foreground sorts:
% 2.46/1.32  
% 2.46/1.32  
% 2.46/1.32  %Background operators:
% 2.46/1.32  
% 2.46/1.32  
% 2.46/1.32  %Foreground operators:
% 2.46/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.46/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.46/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.46/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.46/1.32  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 2.46/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.46/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.46/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.46/1.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.46/1.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.46/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.46/1.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.46/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.46/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.46/1.32  tff(o_1_0_wellord2, type, o_1_0_wellord2: $i > $i).
% 2.46/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.46/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.46/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.46/1.32  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.46/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.46/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.46/1.32  
% 2.46/1.34  tff(f_116, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_2)).
% 2.46/1.34  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.46/1.34  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.46/1.34  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.46/1.34  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.46/1.34  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.46/1.34  tff(f_83, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 2.46/1.34  tff(f_96, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.46/1.34  tff(f_54, axiom, (![A]: m1_subset_1(o_1_0_wellord2(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_1_0_wellord2)).
% 2.46/1.34  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.46/1.34  tff(f_38, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.46/1.34  tff(c_44, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.46/1.34  tff(c_36, plain, (m1_subset_1('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.46/1.34  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.46/1.34  tff(c_71, plain, (![C_51, B_52, A_53]: (v5_relat_1(C_51, B_52) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_53, B_52))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.46/1.34  tff(c_79, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_71])).
% 2.46/1.34  tff(c_46, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.46/1.34  tff(c_4, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.46/1.34  tff(c_55, plain, (![C_44, A_45, B_46]: (v1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.46/1.34  tff(c_63, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_55])).
% 2.46/1.34  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.46/1.34  tff(c_40, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.46/1.34  tff(c_102, plain, (![A_63, B_64, C_65]: (k1_relset_1(A_63, B_64, C_65)=k1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.46/1.34  tff(c_110, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_102])).
% 2.46/1.34  tff(c_170, plain, (![B_80, A_81, C_82]: (k1_xboole_0=B_80 | k1_relset_1(A_81, B_80, C_82)=A_81 | ~v1_funct_2(C_82, A_81, B_80) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.46/1.34  tff(c_173, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_170])).
% 2.46/1.34  tff(c_180, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_110, c_173])).
% 2.46/1.34  tff(c_183, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_180])).
% 2.46/1.34  tff(c_193, plain, (![A_83, B_84, C_85]: (k7_partfun1(A_83, B_84, C_85)=k1_funct_1(B_84, C_85) | ~r2_hidden(C_85, k1_relat_1(B_84)) | ~v1_funct_1(B_84) | ~v5_relat_1(B_84, A_83) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.46/1.34  tff(c_195, plain, (![A_83, C_85]: (k7_partfun1(A_83, '#skF_3', C_85)=k1_funct_1('#skF_3', C_85) | ~r2_hidden(C_85, '#skF_1') | ~v1_funct_1('#skF_3') | ~v5_relat_1('#skF_3', A_83) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_183, c_193])).
% 2.46/1.34  tff(c_202, plain, (![A_86, C_87]: (k7_partfun1(A_86, '#skF_3', C_87)=k1_funct_1('#skF_3', C_87) | ~r2_hidden(C_87, '#skF_1') | ~v5_relat_1('#skF_3', A_86))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_42, c_195])).
% 2.46/1.34  tff(c_205, plain, (![A_86, A_2]: (k7_partfun1(A_86, '#skF_3', A_2)=k1_funct_1('#skF_3', A_2) | ~v5_relat_1('#skF_3', A_86) | v1_xboole_0('#skF_1') | ~m1_subset_1(A_2, '#skF_1'))), inference(resolution, [status(thm)], [c_4, c_202])).
% 2.46/1.34  tff(c_209, plain, (![A_88, A_89]: (k7_partfun1(A_88, '#skF_3', A_89)=k1_funct_1('#skF_3', A_89) | ~v5_relat_1('#skF_3', A_88) | ~m1_subset_1(A_89, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_46, c_205])).
% 2.46/1.34  tff(c_213, plain, (![A_90]: (k7_partfun1('#skF_2', '#skF_3', A_90)=k1_funct_1('#skF_3', A_90) | ~m1_subset_1(A_90, '#skF_1'))), inference(resolution, [status(thm)], [c_79, c_209])).
% 2.46/1.34  tff(c_222, plain, (k7_partfun1('#skF_2', '#skF_3', '#skF_4')=k1_funct_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_213])).
% 2.46/1.34  tff(c_34, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k7_partfun1('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.46/1.34  tff(c_223, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k1_funct_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_222, c_34])).
% 2.46/1.34  tff(c_228, plain, (![A_91, B_92, C_93, D_94]: (k3_funct_2(A_91, B_92, C_93, D_94)=k1_funct_1(C_93, D_94) | ~m1_subset_1(D_94, A_91) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~v1_funct_2(C_93, A_91, B_92) | ~v1_funct_1(C_93) | v1_xboole_0(A_91))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.46/1.34  tff(c_234, plain, (![B_92, C_93]: (k3_funct_2('#skF_1', B_92, C_93, '#skF_4')=k1_funct_1(C_93, '#skF_4') | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_92))) | ~v1_funct_2(C_93, '#skF_1', B_92) | ~v1_funct_1(C_93) | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_228])).
% 2.46/1.34  tff(c_265, plain, (![B_99, C_100]: (k3_funct_2('#skF_1', B_99, C_100, '#skF_4')=k1_funct_1(C_100, '#skF_4') | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_99))) | ~v1_funct_2(C_100, '#skF_1', B_99) | ~v1_funct_1(C_100))), inference(negUnitSimplification, [status(thm)], [c_46, c_234])).
% 2.46/1.34  tff(c_268, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_funct_1('#skF_3', '#skF_4') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_265])).
% 2.46/1.34  tff(c_275, plain, (k3_funct_2('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_funct_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_268])).
% 2.46/1.34  tff(c_277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_223, c_275])).
% 2.46/1.34  tff(c_278, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_180])).
% 2.46/1.34  tff(c_16, plain, (![A_15]: (m1_subset_1(o_1_0_wellord2(A_15), A_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.46/1.34  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.46/1.34  tff(c_50, plain, (![A_42, B_43]: (r2_hidden(A_42, B_43) | v1_xboole_0(B_43) | ~m1_subset_1(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.46/1.34  tff(c_6, plain, (![B_5, A_4]: (~r1_tarski(B_5, A_4) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.46/1.34  tff(c_66, plain, (![B_49, A_50]: (~r1_tarski(B_49, A_50) | v1_xboole_0(B_49) | ~m1_subset_1(A_50, B_49))), inference(resolution, [status(thm)], [c_50, c_6])).
% 2.46/1.34  tff(c_70, plain, (![A_1]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_1, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_66])).
% 2.46/1.34  tff(c_82, plain, (![A_54]: (~m1_subset_1(A_54, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_70])).
% 2.46/1.34  tff(c_87, plain, $false, inference(resolution, [status(thm)], [c_16, c_82])).
% 2.46/1.34  tff(c_88, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_70])).
% 2.46/1.34  tff(c_289, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_278, c_88])).
% 2.46/1.34  tff(c_292, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_289])).
% 2.46/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.34  
% 2.46/1.34  Inference rules
% 2.46/1.34  ----------------------
% 2.46/1.34  #Ref     : 0
% 2.46/1.34  #Sup     : 47
% 2.46/1.34  #Fact    : 0
% 2.46/1.34  #Define  : 0
% 2.46/1.34  #Split   : 2
% 2.46/1.34  #Chain   : 0
% 2.46/1.34  #Close   : 0
% 2.46/1.34  
% 2.46/1.34  Ordering : KBO
% 2.46/1.34  
% 2.46/1.34  Simplification rules
% 2.46/1.34  ----------------------
% 2.46/1.34  #Subsume      : 0
% 2.46/1.34  #Demod        : 48
% 2.46/1.34  #Tautology    : 19
% 2.46/1.34  #SimpNegUnit  : 4
% 2.46/1.34  #BackRed      : 13
% 2.46/1.34  
% 2.46/1.34  #Partial instantiations: 0
% 2.46/1.34  #Strategies tried      : 1
% 2.46/1.34  
% 2.46/1.34  Timing (in seconds)
% 2.46/1.34  ----------------------
% 2.46/1.34  Preprocessing        : 0.31
% 2.46/1.34  Parsing              : 0.16
% 2.46/1.34  CNF conversion       : 0.02
% 2.46/1.34  Main loop            : 0.24
% 2.46/1.34  Inferencing          : 0.09
% 2.46/1.34  Reduction            : 0.08
% 2.46/1.34  Demodulation         : 0.05
% 2.46/1.34  BG Simplification    : 0.02
% 2.46/1.34  Subsumption          : 0.03
% 2.46/1.34  Abstraction          : 0.01
% 2.46/1.34  MUC search           : 0.00
% 2.46/1.34  Cooper               : 0.00
% 2.46/1.34  Total                : 0.59
% 2.46/1.34  Index Insertion      : 0.00
% 2.46/1.34  Index Deletion       : 0.00
% 2.46/1.34  Index Matching       : 0.00
% 2.46/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
