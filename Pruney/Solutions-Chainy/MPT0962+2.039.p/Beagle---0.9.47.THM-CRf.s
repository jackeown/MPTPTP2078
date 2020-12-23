%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:57 EST 2020

% Result     : Theorem 11.33s
% Output     : CNFRefutation 11.39s
% Verified   : 
% Statistics : Number of formulae       :  167 (3384 expanded)
%              Number of leaves         :   26 (1054 expanded)
%              Depth                    :   18
%              Number of atoms          :  295 (7622 expanded)
%              Number of equality atoms :   88 (1524 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_81,axiom,(
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

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_44,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_26,plain,(
    ! [A_14] :
      ( r1_tarski(A_14,k2_zfmisc_1(k1_relat_1(A_14),k2_relat_1(A_14)))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22847,plain,(
    ! [C_1043,A_1044,B_1045] :
      ( r1_tarski(k2_zfmisc_1(C_1043,A_1044),k2_zfmisc_1(C_1043,B_1045))
      | ~ r1_tarski(A_1044,B_1045) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_24567,plain,(
    ! [A_1182,C_1183,B_1184,A_1185] :
      ( r1_tarski(A_1182,k2_zfmisc_1(C_1183,B_1184))
      | ~ r1_tarski(A_1182,k2_zfmisc_1(C_1183,A_1185))
      | ~ r1_tarski(A_1185,B_1184) ) ),
    inference(resolution,[status(thm)],[c_22847,c_8])).

tff(c_24614,plain,(
    ! [A_1186,B_1187] :
      ( r1_tarski(A_1186,k2_zfmisc_1(k1_relat_1(A_1186),B_1187))
      | ~ r1_tarski(k2_relat_1(A_1186),B_1187)
      | ~ v1_relat_1(A_1186) ) ),
    inference(resolution,[status(thm)],[c_26,c_24567])).

tff(c_24,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_46,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_42,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_50,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42])).

tff(c_86,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_205,plain,(
    ! [C_45,A_46,B_47] :
      ( r1_tarski(k2_zfmisc_1(C_45,A_46),k2_zfmisc_1(C_45,B_47))
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2195,plain,(
    ! [A_204,C_205,B_206,A_207] :
      ( r1_tarski(A_204,k2_zfmisc_1(C_205,B_206))
      | ~ r1_tarski(A_204,k2_zfmisc_1(C_205,A_207))
      | ~ r1_tarski(A_207,B_206) ) ),
    inference(resolution,[status(thm)],[c_205,c_8])).

tff(c_2247,plain,(
    ! [A_208,B_209] :
      ( r1_tarski(A_208,k2_zfmisc_1(k1_relat_1(A_208),B_209))
      | ~ r1_tarski(k2_relat_1(A_208),B_209)
      | ~ v1_relat_1(A_208) ) ),
    inference(resolution,[status(thm)],[c_26,c_2195])).

tff(c_267,plain,(
    ! [A_52,B_53,C_54] :
      ( k1_relset_1(A_52,B_53,C_54) = k1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_278,plain,(
    ! [A_52,B_53,A_12] :
      ( k1_relset_1(A_52,B_53,A_12) = k1_relat_1(A_12)
      | ~ r1_tarski(A_12,k2_zfmisc_1(A_52,B_53)) ) ),
    inference(resolution,[status(thm)],[c_24,c_267])).

tff(c_3220,plain,(
    ! [A_253,B_254] :
      ( k1_relset_1(k1_relat_1(A_253),B_254,A_253) = k1_relat_1(A_253)
      | ~ r1_tarski(k2_relat_1(A_253),B_254)
      | ~ v1_relat_1(A_253) ) ),
    inference(resolution,[status(thm)],[c_2247,c_278])).

tff(c_3234,plain,
    ( k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_3220])).

tff(c_3244,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3234])).

tff(c_18,plain,(
    ! [C_11,A_9,B_10] :
      ( r1_tarski(k2_zfmisc_1(C_11,A_9),k2_zfmisc_1(C_11,B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2551,plain,(
    ! [C_222,A_223,B_224,B_225] :
      ( r1_tarski(k2_zfmisc_1(C_222,A_223),k2_zfmisc_1(C_222,B_224))
      | ~ r1_tarski(B_225,B_224)
      | ~ r1_tarski(A_223,B_225) ) ),
    inference(resolution,[status(thm)],[c_18,c_2195])).

tff(c_2631,plain,(
    ! [C_227,A_228] :
      ( r1_tarski(k2_zfmisc_1(C_227,A_228),k2_zfmisc_1(C_227,'#skF_1'))
      | ~ r1_tarski(A_228,k2_relat_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_44,c_2551])).

tff(c_12495,plain,(
    ! [A_469,C_470,A_471] :
      ( r1_tarski(A_469,k2_zfmisc_1(C_470,'#skF_1'))
      | ~ r1_tarski(A_469,k2_zfmisc_1(C_470,A_471))
      | ~ r1_tarski(A_471,k2_relat_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_2631,c_8])).

tff(c_12937,plain,(
    ! [A_484] :
      ( r1_tarski(A_484,k2_zfmisc_1(k1_relat_1(A_484),'#skF_1'))
      | ~ r1_tarski(k2_relat_1(A_484),k2_relat_1('#skF_2'))
      | ~ v1_relat_1(A_484) ) ),
    inference(resolution,[status(thm)],[c_26,c_12495])).

tff(c_12940,plain,
    ( r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_12937])).

tff(c_12943,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_12940])).

tff(c_549,plain,(
    ! [B_73,C_74,A_75] :
      ( k1_xboole_0 = B_73
      | v1_funct_2(C_74,A_75,B_73)
      | k1_relset_1(A_75,B_73,C_74) != A_75
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_566,plain,(
    ! [B_73,A_12,A_75] :
      ( k1_xboole_0 = B_73
      | v1_funct_2(A_12,A_75,B_73)
      | k1_relset_1(A_75,B_73,A_12) != A_75
      | ~ r1_tarski(A_12,k2_zfmisc_1(A_75,B_73)) ) ),
    inference(resolution,[status(thm)],[c_24,c_549])).

tff(c_12962,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12943,c_566])).

tff(c_13004,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3244,c_12962])).

tff(c_13005,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_13004])).

tff(c_14,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_279,plain,(
    ! [A_55,A_56] :
      ( r1_tarski(k2_zfmisc_1(A_55,A_56),k1_xboole_0)
      | ~ r1_tarski(A_56,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_205])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_125,plain,(
    ! [A_34,C_35,B_36] :
      ( r1_tarski(A_34,C_35)
      | ~ r1_tarski(B_36,C_35)
      | ~ r1_tarski(A_34,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_134,plain,(
    ! [A_34,A_6] :
      ( r1_tarski(A_34,A_6)
      | ~ r1_tarski(A_34,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_125])).

tff(c_362,plain,(
    ! [A_62,A_63,A_64] :
      ( r1_tarski(k2_zfmisc_1(A_62,A_63),A_64)
      | ~ r1_tarski(A_63,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_279,c_134])).

tff(c_394,plain,(
    ! [A_3,A_64,A_62,A_63] :
      ( r1_tarski(A_3,A_64)
      | ~ r1_tarski(A_3,k2_zfmisc_1(A_62,A_63))
      | ~ r1_tarski(A_63,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_362,c_8])).

tff(c_2316,plain,(
    ! [A_210,A_211,B_212] :
      ( r1_tarski(A_210,A_211)
      | ~ r1_tarski(B_212,k1_xboole_0)
      | ~ r1_tarski(k2_relat_1(A_210),B_212)
      | ~ v1_relat_1(A_210) ) ),
    inference(resolution,[status(thm)],[c_2247,c_394])).

tff(c_2330,plain,(
    ! [A_211] :
      ( r1_tarski('#skF_2',A_211)
      | ~ r1_tarski('#skF_1',k1_xboole_0)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_2316])).

tff(c_2340,plain,(
    ! [A_211] :
      ( r1_tarski('#skF_2',A_211)
      | ~ r1_tarski('#skF_1',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2330])).

tff(c_2342,plain,(
    ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2340])).

tff(c_13122,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13005,c_2342])).

tff(c_13178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_13122])).

tff(c_13179,plain,(
    ! [A_211] : r1_tarski('#skF_2',A_211) ),
    inference(splitRight,[status(thm)],[c_2340])).

tff(c_13181,plain,(
    ! [A_487] : r1_tarski('#skF_2',A_487) ),
    inference(splitRight,[status(thm)],[c_2340])).

tff(c_87,plain,(
    ! [B_29,A_30] :
      ( B_29 = A_30
      | ~ r1_tarski(B_29,A_30)
      | ~ r1_tarski(A_30,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_87])).

tff(c_13289,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_13181,c_99])).

tff(c_13180,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2340])).

tff(c_13349,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13289,c_13180])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_13353,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_13349,c_2])).

tff(c_13357,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13179,c_13353])).

tff(c_13360,plain,(
    ! [A_211] : r1_tarski('#skF_1',A_211) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13357,c_13179])).

tff(c_94,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_87])).

tff(c_113,plain,(
    ~ r1_tarski('#skF_1',k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_13362,plain,(
    ~ r1_tarski('#skF_1',k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13357,c_113])).

tff(c_13527,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13360,c_13362])).

tff(c_13528,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_13548,plain,(
    ! [A_496] :
      ( r1_tarski(A_496,k2_zfmisc_1(k1_relat_1(A_496),k2_relat_1(A_496)))
      | ~ v1_relat_1(A_496) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_13553,plain,
    ( r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13528,c_13548])).

tff(c_13556,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_13553])).

tff(c_14248,plain,(
    ! [A_543,B_544,C_545] :
      ( k1_relset_1(A_543,B_544,C_545) = k1_relat_1(C_545)
      | ~ m1_subset_1(C_545,k1_zfmisc_1(k2_zfmisc_1(A_543,B_544))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14390,plain,(
    ! [A_558,B_559,A_560] :
      ( k1_relset_1(A_558,B_559,A_560) = k1_relat_1(A_560)
      | ~ r1_tarski(A_560,k2_zfmisc_1(A_558,B_559)) ) ),
    inference(resolution,[status(thm)],[c_24,c_14248])).

tff(c_14445,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_13556,c_14390])).

tff(c_15376,plain,(
    ! [B_630,C_631,A_632] :
      ( k1_xboole_0 = B_630
      | v1_funct_2(C_631,A_632,B_630)
      | k1_relset_1(A_632,B_630,C_631) != A_632
      | ~ m1_subset_1(C_631,k1_zfmisc_1(k2_zfmisc_1(A_632,B_630))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_17611,plain,(
    ! [B_742,A_743,A_744] :
      ( k1_xboole_0 = B_742
      | v1_funct_2(A_743,A_744,B_742)
      | k1_relset_1(A_744,B_742,A_743) != A_744
      | ~ r1_tarski(A_743,k2_zfmisc_1(A_744,B_742)) ) ),
    inference(resolution,[status(thm)],[c_24,c_15376])).

tff(c_17670,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_13556,c_17611])).

tff(c_17702,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14445,c_17670])).

tff(c_17703,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_17702])).

tff(c_13573,plain,(
    ! [C_500,A_501,B_502] :
      ( r1_tarski(k2_zfmisc_1(C_500,A_501),k2_zfmisc_1(C_500,B_502))
      | ~ r1_tarski(A_501,B_502) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_13607,plain,(
    ! [A_505,A_506] :
      ( r1_tarski(k2_zfmisc_1(A_505,A_506),k1_xboole_0)
      | ~ r1_tarski(A_506,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_13573])).

tff(c_13560,plain,(
    ! [A_497,C_498,B_499] :
      ( r1_tarski(A_497,C_498)
      | ~ r1_tarski(B_499,C_498)
      | ~ r1_tarski(A_497,B_499) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_13572,plain,(
    ! [A_497,A_6] :
      ( r1_tarski(A_497,A_6)
      | ~ r1_tarski(A_497,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_13560])).

tff(c_13623,plain,(
    ! [A_505,A_506,A_6] :
      ( r1_tarski(k2_zfmisc_1(A_505,A_506),A_6)
      | ~ r1_tarski(A_506,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_13607,c_13572])).

tff(c_13559,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1') = '#skF_2'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_13556,c_2])).

tff(c_13777,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_13559])).

tff(c_13781,plain,(
    ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_13623,c_13777])).

tff(c_17760,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17703,c_13781])).

tff(c_17774,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_17760])).

tff(c_17775,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_13559])).

tff(c_18728,plain,(
    ! [B_800,A_801,C_802] :
      ( k1_xboole_0 = B_800
      | k1_relset_1(A_801,B_800,C_802) = A_801
      | ~ v1_funct_2(C_802,A_801,B_800)
      | ~ m1_subset_1(C_802,k1_zfmisc_1(k2_zfmisc_1(A_801,B_800))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_18740,plain,(
    ! [C_802] :
      ( k1_xboole_0 = '#skF_1'
      | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1',C_802) = k1_relat_1('#skF_2')
      | ~ v1_funct_2(C_802,k1_relat_1('#skF_2'),'#skF_1')
      | ~ m1_subset_1(C_802,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17775,c_18728])).

tff(c_18786,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_18740])).

tff(c_17792,plain,(
    ! [A_6] :
      ( r1_tarski('#skF_2',A_6)
      | ~ r1_tarski('#skF_1',k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17775,c_13623])).

tff(c_17807,plain,(
    ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_17792])).

tff(c_18808,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18786,c_17807])).

tff(c_18822,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_18808])).

tff(c_18824,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18740])).

tff(c_18085,plain,(
    ! [A_760,B_761,C_762] :
      ( k1_relset_1(A_760,B_761,C_762) = k1_relat_1(C_762)
      | ~ m1_subset_1(C_762,k1_zfmisc_1(k2_zfmisc_1(A_760,B_761))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18414,plain,(
    ! [A_784,B_785,A_786] :
      ( k1_relset_1(A_784,B_785,A_786) = k1_relat_1(A_786)
      | ~ r1_tarski(A_786,k2_zfmisc_1(A_784,B_785)) ) ),
    inference(resolution,[status(thm)],[c_24,c_18085])).

tff(c_18470,plain,(
    ! [A_784,B_785] : k1_relset_1(A_784,B_785,k2_zfmisc_1(A_784,B_785)) = k1_relat_1(k2_zfmisc_1(A_784,B_785)) ),
    inference(resolution,[status(thm)],[c_6,c_18414])).

tff(c_18916,plain,(
    ! [B_811,C_812,A_813] :
      ( k1_xboole_0 = B_811
      | v1_funct_2(C_812,A_813,B_811)
      | k1_relset_1(A_813,B_811,C_812) != A_813
      | ~ m1_subset_1(C_812,k1_zfmisc_1(k2_zfmisc_1(A_813,B_811))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_21774,plain,(
    ! [B_971,A_972,A_973] :
      ( k1_xboole_0 = B_971
      | v1_funct_2(A_972,A_973,B_971)
      | k1_relset_1(A_973,B_971,A_972) != A_973
      | ~ r1_tarski(A_972,k2_zfmisc_1(A_973,B_971)) ) ),
    inference(resolution,[status(thm)],[c_24,c_18916])).

tff(c_21840,plain,(
    ! [B_971,A_973] :
      ( k1_xboole_0 = B_971
      | v1_funct_2(k2_zfmisc_1(A_973,B_971),A_973,B_971)
      | k1_relset_1(A_973,B_971,k2_zfmisc_1(A_973,B_971)) != A_973 ) ),
    inference(resolution,[status(thm)],[c_6,c_21774])).

tff(c_21901,plain,(
    ! [B_977,A_978] :
      ( k1_xboole_0 = B_977
      | v1_funct_2(k2_zfmisc_1(A_978,B_977),A_978,B_977)
      | k1_relat_1(k2_zfmisc_1(A_978,B_977)) != A_978 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18470,c_21840])).

tff(c_21928,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relat_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')) != k1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_17775,c_21901])).

tff(c_21948,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17775,c_21928])).

tff(c_21950,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_18824,c_21948])).

tff(c_21951,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(splitRight,[status(thm)],[c_17792])).

tff(c_21954,plain,(
    ! [A_979] : r1_tarski('#skF_2',A_979) ),
    inference(splitRight,[status(thm)],[c_17792])).

tff(c_21973,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_21954,c_99])).

tff(c_21952,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_17792])).

tff(c_21991,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21973,c_21952])).

tff(c_21995,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_21991,c_2])).

tff(c_21999,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21951,c_21995])).

tff(c_30,plain,(
    ! [A_18] :
      ( v1_funct_2(k1_xboole_0,A_18,k1_xboole_0)
      | k1_xboole_0 = A_18
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_18,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_53,plain,(
    ! [A_18] :
      ( v1_funct_2(k1_xboole_0,A_18,k1_xboole_0)
      | k1_xboole_0 = A_18
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_30])).

tff(c_13761,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_13764,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_13761])).

tff(c_13768,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_13764])).

tff(c_13769,plain,(
    ! [A_18] :
      ( v1_funct_2(k1_xboole_0,A_18,k1_xboole_0)
      | k1_xboole_0 = A_18 ) ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_21975,plain,(
    ! [A_18] :
      ( v1_funct_2('#skF_2',A_18,'#skF_2')
      | A_18 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21973,c_21973,c_21973,c_13769])).

tff(c_22140,plain,(
    ! [A_991] :
      ( v1_funct_2('#skF_1',A_991,'#skF_1')
      | A_991 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21999,c_21999,c_21999,c_21975])).

tff(c_22005,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21999,c_21999,c_86])).

tff(c_22146,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22140,c_22005])).

tff(c_13770,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_21976,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21973,c_21973,c_13770])).

tff(c_22059,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21999,c_21999,c_21976])).

tff(c_16,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_21983,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_2',B_8) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21973,c_21973,c_16])).

tff(c_22065,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_1',B_8) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21999,c_21999,c_21983])).

tff(c_22098,plain,(
    ! [A_985,B_986,C_987] :
      ( k1_relset_1(A_985,B_986,C_987) = k1_relat_1(C_987)
      | ~ m1_subset_1(C_987,k1_zfmisc_1(k2_zfmisc_1(A_985,B_986))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22748,plain,(
    ! [B_1029,C_1030] :
      ( k1_relset_1('#skF_1',B_1029,C_1030) = k1_relat_1(C_1030)
      | ~ m1_subset_1(C_1030,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22065,c_22098])).

tff(c_22750,plain,(
    ! [B_1029] : k1_relset_1('#skF_1',B_1029,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22059,c_22748])).

tff(c_22755,plain,(
    ! [B_1029] : k1_relset_1('#skF_1',B_1029,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22146,c_22750])).

tff(c_22001,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21999,c_21973])).

tff(c_34,plain,(
    ! [C_20,B_19] :
      ( v1_funct_2(C_20,k1_xboole_0,B_19)
      | k1_relset_1(k1_xboole_0,B_19,C_20) != k1_xboole_0
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_52,plain,(
    ! [C_20,B_19] :
      ( v1_funct_2(C_20,k1_xboole_0,B_19)
      | k1_relset_1(k1_xboole_0,B_19,C_20) != k1_xboole_0
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_34])).

tff(c_22237,plain,(
    ! [C_1000,B_1001] :
      ( v1_funct_2(C_1000,'#skF_1',B_1001)
      | k1_relset_1('#skF_1',B_1001,C_1000) != '#skF_1'
      | ~ m1_subset_1(C_1000,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22001,c_22001,c_22001,c_22001,c_52])).

tff(c_22591,plain,(
    ! [B_1022] :
      ( v1_funct_2('#skF_1','#skF_1',B_1022)
      | k1_relset_1('#skF_1',B_1022,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_22059,c_22237])).

tff(c_22151,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22146,c_22005])).

tff(c_22603,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_1') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_22591,c_22151])).

tff(c_22761,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22755,c_22603])).

tff(c_22762,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_22767,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_22762])).

tff(c_24636,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24614,c_22767])).

tff(c_24675,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_24636])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.33/4.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.39/4.07  
% 11.39/4.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.39/4.07  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 11.39/4.07  
% 11.39/4.07  %Foreground sorts:
% 11.39/4.07  
% 11.39/4.07  
% 11.39/4.07  %Background operators:
% 11.39/4.07  
% 11.39/4.07  
% 11.39/4.07  %Foreground operators:
% 11.39/4.07  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.39/4.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.39/4.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.39/4.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.39/4.07  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.39/4.07  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.39/4.07  tff('#skF_2', type, '#skF_2': $i).
% 11.39/4.07  tff('#skF_1', type, '#skF_1': $i).
% 11.39/4.07  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.39/4.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.39/4.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.39/4.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.39/4.07  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.39/4.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.39/4.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.39/4.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.39/4.07  
% 11.39/4.09  tff(f_94, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 11.39/4.09  tff(f_59, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 11.39/4.09  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 11.39/4.09  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 11.39/4.09  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.39/4.09  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.39/4.09  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.39/4.09  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 11.39/4.09  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.39/4.09  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.39/4.09  tff(c_48, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.39/4.09  tff(c_44, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.39/4.09  tff(c_26, plain, (![A_14]: (r1_tarski(A_14, k2_zfmisc_1(k1_relat_1(A_14), k2_relat_1(A_14))) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.39/4.09  tff(c_22847, plain, (![C_1043, A_1044, B_1045]: (r1_tarski(k2_zfmisc_1(C_1043, A_1044), k2_zfmisc_1(C_1043, B_1045)) | ~r1_tarski(A_1044, B_1045))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.39/4.09  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.39/4.09  tff(c_24567, plain, (![A_1182, C_1183, B_1184, A_1185]: (r1_tarski(A_1182, k2_zfmisc_1(C_1183, B_1184)) | ~r1_tarski(A_1182, k2_zfmisc_1(C_1183, A_1185)) | ~r1_tarski(A_1185, B_1184))), inference(resolution, [status(thm)], [c_22847, c_8])).
% 11.39/4.09  tff(c_24614, plain, (![A_1186, B_1187]: (r1_tarski(A_1186, k2_zfmisc_1(k1_relat_1(A_1186), B_1187)) | ~r1_tarski(k2_relat_1(A_1186), B_1187) | ~v1_relat_1(A_1186))), inference(resolution, [status(thm)], [c_26, c_24567])).
% 11.39/4.09  tff(c_24, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.39/4.09  tff(c_46, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.39/4.09  tff(c_42, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.39/4.09  tff(c_50, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42])).
% 11.39/4.09  tff(c_86, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 11.39/4.09  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.39/4.09  tff(c_205, plain, (![C_45, A_46, B_47]: (r1_tarski(k2_zfmisc_1(C_45, A_46), k2_zfmisc_1(C_45, B_47)) | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.39/4.09  tff(c_2195, plain, (![A_204, C_205, B_206, A_207]: (r1_tarski(A_204, k2_zfmisc_1(C_205, B_206)) | ~r1_tarski(A_204, k2_zfmisc_1(C_205, A_207)) | ~r1_tarski(A_207, B_206))), inference(resolution, [status(thm)], [c_205, c_8])).
% 11.39/4.09  tff(c_2247, plain, (![A_208, B_209]: (r1_tarski(A_208, k2_zfmisc_1(k1_relat_1(A_208), B_209)) | ~r1_tarski(k2_relat_1(A_208), B_209) | ~v1_relat_1(A_208))), inference(resolution, [status(thm)], [c_26, c_2195])).
% 11.39/4.09  tff(c_267, plain, (![A_52, B_53, C_54]: (k1_relset_1(A_52, B_53, C_54)=k1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.39/4.09  tff(c_278, plain, (![A_52, B_53, A_12]: (k1_relset_1(A_52, B_53, A_12)=k1_relat_1(A_12) | ~r1_tarski(A_12, k2_zfmisc_1(A_52, B_53)))), inference(resolution, [status(thm)], [c_24, c_267])).
% 11.39/4.09  tff(c_3220, plain, (![A_253, B_254]: (k1_relset_1(k1_relat_1(A_253), B_254, A_253)=k1_relat_1(A_253) | ~r1_tarski(k2_relat_1(A_253), B_254) | ~v1_relat_1(A_253))), inference(resolution, [status(thm)], [c_2247, c_278])).
% 11.39/4.09  tff(c_3234, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_44, c_3220])).
% 11.39/4.09  tff(c_3244, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3234])).
% 11.39/4.09  tff(c_18, plain, (![C_11, A_9, B_10]: (r1_tarski(k2_zfmisc_1(C_11, A_9), k2_zfmisc_1(C_11, B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.39/4.09  tff(c_2551, plain, (![C_222, A_223, B_224, B_225]: (r1_tarski(k2_zfmisc_1(C_222, A_223), k2_zfmisc_1(C_222, B_224)) | ~r1_tarski(B_225, B_224) | ~r1_tarski(A_223, B_225))), inference(resolution, [status(thm)], [c_18, c_2195])).
% 11.39/4.09  tff(c_2631, plain, (![C_227, A_228]: (r1_tarski(k2_zfmisc_1(C_227, A_228), k2_zfmisc_1(C_227, '#skF_1')) | ~r1_tarski(A_228, k2_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_44, c_2551])).
% 11.39/4.09  tff(c_12495, plain, (![A_469, C_470, A_471]: (r1_tarski(A_469, k2_zfmisc_1(C_470, '#skF_1')) | ~r1_tarski(A_469, k2_zfmisc_1(C_470, A_471)) | ~r1_tarski(A_471, k2_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_2631, c_8])).
% 11.39/4.09  tff(c_12937, plain, (![A_484]: (r1_tarski(A_484, k2_zfmisc_1(k1_relat_1(A_484), '#skF_1')) | ~r1_tarski(k2_relat_1(A_484), k2_relat_1('#skF_2')) | ~v1_relat_1(A_484))), inference(resolution, [status(thm)], [c_26, c_12495])).
% 11.39/4.09  tff(c_12940, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_6, c_12937])).
% 11.39/4.09  tff(c_12943, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_12940])).
% 11.39/4.09  tff(c_549, plain, (![B_73, C_74, A_75]: (k1_xboole_0=B_73 | v1_funct_2(C_74, A_75, B_73) | k1_relset_1(A_75, B_73, C_74)!=A_75 | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_73))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.39/4.09  tff(c_566, plain, (![B_73, A_12, A_75]: (k1_xboole_0=B_73 | v1_funct_2(A_12, A_75, B_73) | k1_relset_1(A_75, B_73, A_12)!=A_75 | ~r1_tarski(A_12, k2_zfmisc_1(A_75, B_73)))), inference(resolution, [status(thm)], [c_24, c_549])).
% 11.39/4.09  tff(c_12962, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12943, c_566])).
% 11.39/4.09  tff(c_13004, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3244, c_12962])).
% 11.39/4.09  tff(c_13005, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_86, c_13004])).
% 11.39/4.09  tff(c_14, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.39/4.09  tff(c_279, plain, (![A_55, A_56]: (r1_tarski(k2_zfmisc_1(A_55, A_56), k1_xboole_0) | ~r1_tarski(A_56, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_205])).
% 11.39/4.09  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.39/4.09  tff(c_125, plain, (![A_34, C_35, B_36]: (r1_tarski(A_34, C_35) | ~r1_tarski(B_36, C_35) | ~r1_tarski(A_34, B_36))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.39/4.09  tff(c_134, plain, (![A_34, A_6]: (r1_tarski(A_34, A_6) | ~r1_tarski(A_34, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_125])).
% 11.39/4.09  tff(c_362, plain, (![A_62, A_63, A_64]: (r1_tarski(k2_zfmisc_1(A_62, A_63), A_64) | ~r1_tarski(A_63, k1_xboole_0))), inference(resolution, [status(thm)], [c_279, c_134])).
% 11.39/4.09  tff(c_394, plain, (![A_3, A_64, A_62, A_63]: (r1_tarski(A_3, A_64) | ~r1_tarski(A_3, k2_zfmisc_1(A_62, A_63)) | ~r1_tarski(A_63, k1_xboole_0))), inference(resolution, [status(thm)], [c_362, c_8])).
% 11.39/4.10  tff(c_2316, plain, (![A_210, A_211, B_212]: (r1_tarski(A_210, A_211) | ~r1_tarski(B_212, k1_xboole_0) | ~r1_tarski(k2_relat_1(A_210), B_212) | ~v1_relat_1(A_210))), inference(resolution, [status(thm)], [c_2247, c_394])).
% 11.39/4.10  tff(c_2330, plain, (![A_211]: (r1_tarski('#skF_2', A_211) | ~r1_tarski('#skF_1', k1_xboole_0) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_2316])).
% 11.39/4.10  tff(c_2340, plain, (![A_211]: (r1_tarski('#skF_2', A_211) | ~r1_tarski('#skF_1', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2330])).
% 11.39/4.10  tff(c_2342, plain, (~r1_tarski('#skF_1', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2340])).
% 11.39/4.10  tff(c_13122, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13005, c_2342])).
% 11.39/4.10  tff(c_13178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_13122])).
% 11.39/4.10  tff(c_13179, plain, (![A_211]: (r1_tarski('#skF_2', A_211))), inference(splitRight, [status(thm)], [c_2340])).
% 11.39/4.10  tff(c_13181, plain, (![A_487]: (r1_tarski('#skF_2', A_487))), inference(splitRight, [status(thm)], [c_2340])).
% 11.39/4.10  tff(c_87, plain, (![B_29, A_30]: (B_29=A_30 | ~r1_tarski(B_29, A_30) | ~r1_tarski(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.39/4.10  tff(c_99, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_87])).
% 11.39/4.10  tff(c_13289, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_13181, c_99])).
% 11.39/4.10  tff(c_13180, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(splitRight, [status(thm)], [c_2340])).
% 11.39/4.10  tff(c_13349, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13289, c_13180])).
% 11.39/4.10  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.39/4.10  tff(c_13353, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_13349, c_2])).
% 11.39/4.10  tff(c_13357, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13179, c_13353])).
% 11.39/4.10  tff(c_13360, plain, (![A_211]: (r1_tarski('#skF_1', A_211))), inference(demodulation, [status(thm), theory('equality')], [c_13357, c_13179])).
% 11.39/4.10  tff(c_94, plain, (k2_relat_1('#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_87])).
% 11.39/4.10  tff(c_113, plain, (~r1_tarski('#skF_1', k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_94])).
% 11.39/4.10  tff(c_13362, plain, (~r1_tarski('#skF_1', k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_13357, c_113])).
% 11.39/4.10  tff(c_13527, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13360, c_13362])).
% 11.39/4.10  tff(c_13528, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_94])).
% 11.39/4.10  tff(c_13548, plain, (![A_496]: (r1_tarski(A_496, k2_zfmisc_1(k1_relat_1(A_496), k2_relat_1(A_496))) | ~v1_relat_1(A_496))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.39/4.10  tff(c_13553, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13528, c_13548])).
% 11.39/4.10  tff(c_13556, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_13553])).
% 11.39/4.10  tff(c_14248, plain, (![A_543, B_544, C_545]: (k1_relset_1(A_543, B_544, C_545)=k1_relat_1(C_545) | ~m1_subset_1(C_545, k1_zfmisc_1(k2_zfmisc_1(A_543, B_544))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.39/4.10  tff(c_14390, plain, (![A_558, B_559, A_560]: (k1_relset_1(A_558, B_559, A_560)=k1_relat_1(A_560) | ~r1_tarski(A_560, k2_zfmisc_1(A_558, B_559)))), inference(resolution, [status(thm)], [c_24, c_14248])).
% 11.39/4.10  tff(c_14445, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_13556, c_14390])).
% 11.39/4.10  tff(c_15376, plain, (![B_630, C_631, A_632]: (k1_xboole_0=B_630 | v1_funct_2(C_631, A_632, B_630) | k1_relset_1(A_632, B_630, C_631)!=A_632 | ~m1_subset_1(C_631, k1_zfmisc_1(k2_zfmisc_1(A_632, B_630))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.39/4.10  tff(c_17611, plain, (![B_742, A_743, A_744]: (k1_xboole_0=B_742 | v1_funct_2(A_743, A_744, B_742) | k1_relset_1(A_744, B_742, A_743)!=A_744 | ~r1_tarski(A_743, k2_zfmisc_1(A_744, B_742)))), inference(resolution, [status(thm)], [c_24, c_15376])).
% 11.39/4.10  tff(c_17670, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_13556, c_17611])).
% 11.39/4.10  tff(c_17702, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14445, c_17670])).
% 11.39/4.10  tff(c_17703, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_86, c_17702])).
% 11.39/4.10  tff(c_13573, plain, (![C_500, A_501, B_502]: (r1_tarski(k2_zfmisc_1(C_500, A_501), k2_zfmisc_1(C_500, B_502)) | ~r1_tarski(A_501, B_502))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.39/4.10  tff(c_13607, plain, (![A_505, A_506]: (r1_tarski(k2_zfmisc_1(A_505, A_506), k1_xboole_0) | ~r1_tarski(A_506, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_13573])).
% 11.39/4.10  tff(c_13560, plain, (![A_497, C_498, B_499]: (r1_tarski(A_497, C_498) | ~r1_tarski(B_499, C_498) | ~r1_tarski(A_497, B_499))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.39/4.10  tff(c_13572, plain, (![A_497, A_6]: (r1_tarski(A_497, A_6) | ~r1_tarski(A_497, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_13560])).
% 11.39/4.10  tff(c_13623, plain, (![A_505, A_506, A_6]: (r1_tarski(k2_zfmisc_1(A_505, A_506), A_6) | ~r1_tarski(A_506, k1_xboole_0))), inference(resolution, [status(thm)], [c_13607, c_13572])).
% 11.39/4.10  tff(c_13559, plain, (k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')='#skF_2' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_13556, c_2])).
% 11.39/4.10  tff(c_13777, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_13559])).
% 11.39/4.10  tff(c_13781, plain, (~r1_tarski('#skF_1', k1_xboole_0)), inference(resolution, [status(thm)], [c_13623, c_13777])).
% 11.39/4.10  tff(c_17760, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17703, c_13781])).
% 11.39/4.10  tff(c_17774, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_17760])).
% 11.39/4.10  tff(c_17775, plain, (k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_13559])).
% 11.39/4.10  tff(c_18728, plain, (![B_800, A_801, C_802]: (k1_xboole_0=B_800 | k1_relset_1(A_801, B_800, C_802)=A_801 | ~v1_funct_2(C_802, A_801, B_800) | ~m1_subset_1(C_802, k1_zfmisc_1(k2_zfmisc_1(A_801, B_800))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.39/4.10  tff(c_18740, plain, (![C_802]: (k1_xboole_0='#skF_1' | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', C_802)=k1_relat_1('#skF_2') | ~v1_funct_2(C_802, k1_relat_1('#skF_2'), '#skF_1') | ~m1_subset_1(C_802, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_17775, c_18728])).
% 11.39/4.10  tff(c_18786, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_18740])).
% 11.39/4.10  tff(c_17792, plain, (![A_6]: (r1_tarski('#skF_2', A_6) | ~r1_tarski('#skF_1', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_17775, c_13623])).
% 11.39/4.10  tff(c_17807, plain, (~r1_tarski('#skF_1', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_17792])).
% 11.39/4.10  tff(c_18808, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18786, c_17807])).
% 11.39/4.10  tff(c_18822, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_18808])).
% 11.39/4.10  tff(c_18824, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_18740])).
% 11.39/4.10  tff(c_18085, plain, (![A_760, B_761, C_762]: (k1_relset_1(A_760, B_761, C_762)=k1_relat_1(C_762) | ~m1_subset_1(C_762, k1_zfmisc_1(k2_zfmisc_1(A_760, B_761))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.39/4.10  tff(c_18414, plain, (![A_784, B_785, A_786]: (k1_relset_1(A_784, B_785, A_786)=k1_relat_1(A_786) | ~r1_tarski(A_786, k2_zfmisc_1(A_784, B_785)))), inference(resolution, [status(thm)], [c_24, c_18085])).
% 11.39/4.10  tff(c_18470, plain, (![A_784, B_785]: (k1_relset_1(A_784, B_785, k2_zfmisc_1(A_784, B_785))=k1_relat_1(k2_zfmisc_1(A_784, B_785)))), inference(resolution, [status(thm)], [c_6, c_18414])).
% 11.39/4.10  tff(c_18916, plain, (![B_811, C_812, A_813]: (k1_xboole_0=B_811 | v1_funct_2(C_812, A_813, B_811) | k1_relset_1(A_813, B_811, C_812)!=A_813 | ~m1_subset_1(C_812, k1_zfmisc_1(k2_zfmisc_1(A_813, B_811))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.39/4.10  tff(c_21774, plain, (![B_971, A_972, A_973]: (k1_xboole_0=B_971 | v1_funct_2(A_972, A_973, B_971) | k1_relset_1(A_973, B_971, A_972)!=A_973 | ~r1_tarski(A_972, k2_zfmisc_1(A_973, B_971)))), inference(resolution, [status(thm)], [c_24, c_18916])).
% 11.39/4.10  tff(c_21840, plain, (![B_971, A_973]: (k1_xboole_0=B_971 | v1_funct_2(k2_zfmisc_1(A_973, B_971), A_973, B_971) | k1_relset_1(A_973, B_971, k2_zfmisc_1(A_973, B_971))!=A_973)), inference(resolution, [status(thm)], [c_6, c_21774])).
% 11.39/4.10  tff(c_21901, plain, (![B_977, A_978]: (k1_xboole_0=B_977 | v1_funct_2(k2_zfmisc_1(A_978, B_977), A_978, B_977) | k1_relat_1(k2_zfmisc_1(A_978, B_977))!=A_978)), inference(demodulation, [status(thm), theory('equality')], [c_18470, c_21840])).
% 11.39/4.10  tff(c_21928, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relat_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))!=k1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_17775, c_21901])).
% 11.39/4.10  tff(c_21948, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17775, c_21928])).
% 11.39/4.10  tff(c_21950, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_18824, c_21948])).
% 11.39/4.10  tff(c_21951, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(splitRight, [status(thm)], [c_17792])).
% 11.39/4.10  tff(c_21954, plain, (![A_979]: (r1_tarski('#skF_2', A_979))), inference(splitRight, [status(thm)], [c_17792])).
% 11.39/4.10  tff(c_21973, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_21954, c_99])).
% 11.39/4.10  tff(c_21952, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(splitRight, [status(thm)], [c_17792])).
% 11.39/4.10  tff(c_21991, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_21973, c_21952])).
% 11.39/4.10  tff(c_21995, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_21991, c_2])).
% 11.39/4.10  tff(c_21999, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_21951, c_21995])).
% 11.39/4.10  tff(c_30, plain, (![A_18]: (v1_funct_2(k1_xboole_0, A_18, k1_xboole_0) | k1_xboole_0=A_18 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_18, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.39/4.10  tff(c_53, plain, (![A_18]: (v1_funct_2(k1_xboole_0, A_18, k1_xboole_0) | k1_xboole_0=A_18 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_30])).
% 11.39/4.10  tff(c_13761, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_53])).
% 11.39/4.10  tff(c_13764, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_13761])).
% 11.39/4.10  tff(c_13768, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_13764])).
% 11.39/4.10  tff(c_13769, plain, (![A_18]: (v1_funct_2(k1_xboole_0, A_18, k1_xboole_0) | k1_xboole_0=A_18)), inference(splitRight, [status(thm)], [c_53])).
% 11.39/4.10  tff(c_21975, plain, (![A_18]: (v1_funct_2('#skF_2', A_18, '#skF_2') | A_18='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_21973, c_21973, c_21973, c_13769])).
% 11.39/4.10  tff(c_22140, plain, (![A_991]: (v1_funct_2('#skF_1', A_991, '#skF_1') | A_991='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_21999, c_21999, c_21999, c_21975])).
% 11.39/4.10  tff(c_22005, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_21999, c_21999, c_86])).
% 11.39/4.10  tff(c_22146, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_22140, c_22005])).
% 11.39/4.10  tff(c_13770, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_53])).
% 11.39/4.10  tff(c_21976, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_21973, c_21973, c_13770])).
% 11.39/4.10  tff(c_22059, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_21999, c_21999, c_21976])).
% 11.39/4.10  tff(c_16, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.39/4.10  tff(c_21983, plain, (![B_8]: (k2_zfmisc_1('#skF_2', B_8)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_21973, c_21973, c_16])).
% 11.39/4.10  tff(c_22065, plain, (![B_8]: (k2_zfmisc_1('#skF_1', B_8)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_21999, c_21999, c_21983])).
% 11.39/4.10  tff(c_22098, plain, (![A_985, B_986, C_987]: (k1_relset_1(A_985, B_986, C_987)=k1_relat_1(C_987) | ~m1_subset_1(C_987, k1_zfmisc_1(k2_zfmisc_1(A_985, B_986))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.39/4.10  tff(c_22748, plain, (![B_1029, C_1030]: (k1_relset_1('#skF_1', B_1029, C_1030)=k1_relat_1(C_1030) | ~m1_subset_1(C_1030, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_22065, c_22098])).
% 11.39/4.10  tff(c_22750, plain, (![B_1029]: (k1_relset_1('#skF_1', B_1029, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_22059, c_22748])).
% 11.39/4.10  tff(c_22755, plain, (![B_1029]: (k1_relset_1('#skF_1', B_1029, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22146, c_22750])).
% 11.39/4.10  tff(c_22001, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_21999, c_21973])).
% 11.39/4.10  tff(c_34, plain, (![C_20, B_19]: (v1_funct_2(C_20, k1_xboole_0, B_19) | k1_relset_1(k1_xboole_0, B_19, C_20)!=k1_xboole_0 | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_19))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.39/4.10  tff(c_52, plain, (![C_20, B_19]: (v1_funct_2(C_20, k1_xboole_0, B_19) | k1_relset_1(k1_xboole_0, B_19, C_20)!=k1_xboole_0 | ~m1_subset_1(C_20, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_34])).
% 11.39/4.10  tff(c_22237, plain, (![C_1000, B_1001]: (v1_funct_2(C_1000, '#skF_1', B_1001) | k1_relset_1('#skF_1', B_1001, C_1000)!='#skF_1' | ~m1_subset_1(C_1000, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_22001, c_22001, c_22001, c_22001, c_52])).
% 11.39/4.10  tff(c_22591, plain, (![B_1022]: (v1_funct_2('#skF_1', '#skF_1', B_1022) | k1_relset_1('#skF_1', B_1022, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_22059, c_22237])).
% 11.39/4.10  tff(c_22151, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22146, c_22005])).
% 11.39/4.10  tff(c_22603, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_1')!='#skF_1'), inference(resolution, [status(thm)], [c_22591, c_22151])).
% 11.39/4.10  tff(c_22761, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22755, c_22603])).
% 11.39/4.10  tff(c_22762, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')))), inference(splitRight, [status(thm)], [c_50])).
% 11.39/4.10  tff(c_22767, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_24, c_22762])).
% 11.39/4.10  tff(c_24636, plain, (~r1_tarski(k2_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_24614, c_22767])).
% 11.39/4.10  tff(c_24675, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_24636])).
% 11.39/4.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.39/4.10  
% 11.39/4.10  Inference rules
% 11.39/4.10  ----------------------
% 11.39/4.10  #Ref     : 0
% 11.39/4.10  #Sup     : 6262
% 11.39/4.10  #Fact    : 0
% 11.39/4.10  #Define  : 0
% 11.39/4.10  #Split   : 24
% 11.39/4.10  #Chain   : 0
% 11.39/4.10  #Close   : 0
% 11.39/4.10  
% 11.39/4.10  Ordering : KBO
% 11.39/4.10  
% 11.39/4.10  Simplification rules
% 11.39/4.10  ----------------------
% 11.39/4.10  #Subsume      : 1475
% 11.39/4.10  #Demod        : 3220
% 11.39/4.10  #Tautology    : 2226
% 11.39/4.10  #SimpNegUnit  : 27
% 11.39/4.10  #BackRed      : 286
% 11.39/4.10  
% 11.39/4.10  #Partial instantiations: 0
% 11.39/4.10  #Strategies tried      : 1
% 11.39/4.10  
% 11.39/4.10  Timing (in seconds)
% 11.39/4.10  ----------------------
% 11.39/4.10  Preprocessing        : 0.31
% 11.39/4.10  Parsing              : 0.16
% 11.39/4.10  CNF conversion       : 0.02
% 11.39/4.10  Main loop            : 2.95
% 11.39/4.10  Inferencing          : 0.75
% 11.39/4.10  Reduction            : 0.76
% 11.39/4.10  Demodulation         : 0.53
% 11.39/4.10  BG Simplification    : 0.10
% 11.39/4.10  Subsumption          : 1.14
% 11.39/4.10  Abstraction          : 0.14
% 11.39/4.10  MUC search           : 0.00
% 11.39/4.10  Cooper               : 0.00
% 11.39/4.10  Total                : 3.31
% 11.39/4.10  Index Insertion      : 0.00
% 11.39/4.10  Index Deletion       : 0.00
% 11.39/4.10  Index Matching       : 0.00
% 11.39/4.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
