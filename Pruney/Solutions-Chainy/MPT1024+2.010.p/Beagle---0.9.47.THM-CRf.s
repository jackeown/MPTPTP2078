%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:23 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 4.18s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 588 expanded)
%              Number of leaves         :   34 ( 218 expanded)
%              Depth                    :   12
%              Number of atoms          :  158 (1835 expanded)
%              Number of equality atoms :   51 ( 657 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
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

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_96,axiom,(
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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_72,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_81,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_72])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_205,plain,(
    ! [A_94,B_95,C_96,D_97] :
      ( k7_relset_1(A_94,B_95,C_96,D_97) = k9_relat_1(C_96,D_97)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_212,plain,(
    ! [D_97] : k7_relset_1('#skF_2','#skF_3','#skF_5',D_97) = k9_relat_1('#skF_5',D_97) ),
    inference(resolution,[status(thm)],[c_50,c_205])).

tff(c_48,plain,(
    r2_hidden('#skF_6',k7_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_243,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_48])).

tff(c_853,plain,(
    ! [A_203,B_204,C_205] :
      ( r2_hidden(k4_tarski('#skF_1'(A_203,B_204,C_205),A_203),C_205)
      | ~ r2_hidden(A_203,k9_relat_1(C_205,B_204))
      | ~ v1_relat_1(C_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [C_17,A_15,B_16] :
      ( k1_funct_1(C_17,A_15) = B_16
      | ~ r2_hidden(k4_tarski(A_15,B_16),C_17)
      | ~ v1_funct_1(C_17)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1167,plain,(
    ! [C_262,A_263,B_264] :
      ( k1_funct_1(C_262,'#skF_1'(A_263,B_264,C_262)) = A_263
      | ~ v1_funct_1(C_262)
      | ~ r2_hidden(A_263,k9_relat_1(C_262,B_264))
      | ~ v1_relat_1(C_262) ) ),
    inference(resolution,[status(thm)],[c_853,c_22])).

tff(c_1172,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_243,c_1167])).

tff(c_1182,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_54,c_1172])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] :
      ( r2_hidden('#skF_1'(A_9,B_10,C_11),B_10)
      | ~ r2_hidden(A_9,k9_relat_1(C_11,B_10))
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_52,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_124,plain,(
    ! [A_59,B_60,C_61] :
      ( k1_relset_1(A_59,B_60,C_61) = k1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_133,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_124])).

tff(c_1036,plain,(
    ! [B_238,A_239,C_240] :
      ( k1_xboole_0 = B_238
      | k1_relset_1(A_239,B_238,C_240) = A_239
      | ~ v1_funct_2(C_240,A_239,B_238)
      | ~ m1_subset_1(C_240,k1_zfmisc_1(k2_zfmisc_1(A_239,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1043,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1036])).

tff(c_1047,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_133,c_1043])).

tff(c_1048,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1047])).

tff(c_18,plain,(
    ! [A_9,B_10,C_11] :
      ( r2_hidden('#skF_1'(A_9,B_10,C_11),k1_relat_1(C_11))
      | ~ r2_hidden(A_9,k9_relat_1(C_11,B_10))
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1056,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_1'(A_9,B_10,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_9,k9_relat_1('#skF_5',B_10))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1048,c_18])).

tff(c_1088,plain,(
    ! [A_243,B_244] :
      ( r2_hidden('#skF_1'(A_243,B_244,'#skF_5'),'#skF_2')
      | ~ r2_hidden(A_243,k9_relat_1('#skF_5',B_244)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_1056])).

tff(c_46,plain,(
    ! [F_37] :
      ( k1_funct_1('#skF_5',F_37) != '#skF_6'
      | ~ r2_hidden(F_37,'#skF_4')
      | ~ r2_hidden(F_37,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1199,plain,(
    ! [A_265,B_266] :
      ( k1_funct_1('#skF_5','#skF_1'(A_265,B_266,'#skF_5')) != '#skF_6'
      | ~ r2_hidden('#skF_1'(A_265,B_266,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_265,k9_relat_1('#skF_5',B_266)) ) ),
    inference(resolution,[status(thm)],[c_1088,c_46])).

tff(c_1203,plain,(
    ! [A_9] :
      ( k1_funct_1('#skF_5','#skF_1'(A_9,'#skF_4','#skF_5')) != '#skF_6'
      | ~ r2_hidden(A_9,k9_relat_1('#skF_5','#skF_4'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_14,c_1199])).

tff(c_1207,plain,(
    ! [A_267] :
      ( k1_funct_1('#skF_5','#skF_1'(A_267,'#skF_4','#skF_5')) != '#skF_6'
      | ~ r2_hidden(A_267,k9_relat_1('#skF_5','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_1203])).

tff(c_1214,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_6','#skF_4','#skF_5')) != '#skF_6' ),
    inference(resolution,[status(thm)],[c_243,c_1207])).

tff(c_1227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1182,c_1214])).

tff(c_1228,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1047])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,k1_zfmisc_1(B_3))
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_82,plain,(
    ! [A_50,A_51,B_52] :
      ( v1_relat_1(A_50)
      | ~ r1_tarski(A_50,k2_zfmisc_1(A_51,B_52)) ) ),
    inference(resolution,[status(thm)],[c_6,c_72])).

tff(c_92,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_82])).

tff(c_26,plain,(
    ! [B_19,A_18] :
      ( ~ r1_tarski(B_19,A_18)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_922,plain,(
    ! [C_214,A_215,B_216] :
      ( ~ r1_tarski(C_214,k4_tarski('#skF_1'(A_215,B_216,C_214),A_215))
      | ~ r2_hidden(A_215,k9_relat_1(C_214,B_216))
      | ~ v1_relat_1(C_214) ) ),
    inference(resolution,[status(thm)],[c_853,c_26])).

tff(c_926,plain,(
    ! [A_215,B_216] :
      ( ~ r2_hidden(A_215,k9_relat_1(k1_xboole_0,B_216))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_922])).

tff(c_929,plain,(
    ! [A_215,B_216] : ~ r2_hidden(A_215,k9_relat_1(k1_xboole_0,B_216)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_926])).

tff(c_1236,plain,(
    ! [A_215,B_216] : ~ r2_hidden(A_215,k9_relat_1('#skF_3',B_216)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1228,c_929])).

tff(c_59,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_59])).

tff(c_187,plain,(
    ! [C_87,A_88] :
      ( k1_xboole_0 = C_87
      | ~ v1_funct_2(C_87,A_88,k1_xboole_0)
      | k1_xboole_0 = A_88
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_192,plain,(
    ! [A_2,A_88] :
      ( k1_xboole_0 = A_2
      | ~ v1_funct_2(A_2,A_88,k1_xboole_0)
      | k1_xboole_0 = A_88
      | ~ r1_tarski(A_2,k2_zfmisc_1(A_88,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_6,c_187])).

tff(c_1370,plain,(
    ! [A_281,A_282] :
      ( A_281 = '#skF_3'
      | ~ v1_funct_2(A_281,A_282,'#skF_3')
      | A_282 = '#skF_3'
      | ~ r1_tarski(A_281,k2_zfmisc_1(A_282,'#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1228,c_1228,c_1228,c_1228,c_192])).

tff(c_1377,plain,
    ( '#skF_5' = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_67,c_1370])).

tff(c_1382,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1377])).

tff(c_1383,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1382])).

tff(c_1229,plain,(
    k1_relat_1('#skF_5') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1047])).

tff(c_1384,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1383,c_1229])).

tff(c_1394,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1383,c_52])).

tff(c_1390,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1383,c_133])).

tff(c_1392,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1383,c_67])).

tff(c_840,plain,(
    ! [B_199,C_200] :
      ( k1_relset_1(k1_xboole_0,B_199,C_200) = k1_xboole_0
      | ~ v1_funct_2(C_200,k1_xboole_0,B_199)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_199))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_845,plain,(
    ! [B_199,A_2] :
      ( k1_relset_1(k1_xboole_0,B_199,A_2) = k1_xboole_0
      | ~ v1_funct_2(A_2,k1_xboole_0,B_199)
      | ~ r1_tarski(A_2,k2_zfmisc_1(k1_xboole_0,B_199)) ) ),
    inference(resolution,[status(thm)],[c_6,c_840])).

tff(c_1454,plain,(
    ! [B_283,A_284] :
      ( k1_relset_1('#skF_3',B_283,A_284) = '#skF_3'
      | ~ v1_funct_2(A_284,'#skF_3',B_283)
      | ~ r1_tarski(A_284,k2_zfmisc_1('#skF_3',B_283)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1228,c_1228,c_1228,c_1228,c_845])).

tff(c_1457,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_1392,c_1454])).

tff(c_1464,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1394,c_1390,c_1457])).

tff(c_1466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1384,c_1464])).

tff(c_1467,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1382])).

tff(c_1472,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1467,c_243])).

tff(c_1484,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1236,c_1472])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:22:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.84/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.73  
% 3.84/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.73  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.84/1.73  
% 3.84/1.73  %Foreground sorts:
% 3.84/1.73  
% 3.84/1.73  
% 3.84/1.73  %Background operators:
% 3.84/1.73  
% 3.84/1.73  
% 3.84/1.73  %Foreground operators:
% 3.84/1.73  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.84/1.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.84/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.84/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.84/1.73  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.84/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.84/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.84/1.73  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.84/1.73  tff('#skF_5', type, '#skF_5': $i).
% 3.84/1.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.84/1.73  tff('#skF_6', type, '#skF_6': $i).
% 3.84/1.73  tff('#skF_2', type, '#skF_2': $i).
% 3.84/1.73  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.84/1.73  tff('#skF_3', type, '#skF_3': $i).
% 3.84/1.73  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.84/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.84/1.73  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.84/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.84/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.84/1.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.84/1.73  tff('#skF_4', type, '#skF_4': $i).
% 3.84/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.84/1.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.84/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.84/1.73  
% 4.18/1.75  tff(f_115, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 4.18/1.75  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.18/1.75  tff(f_78, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.18/1.75  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 4.18/1.75  tff(f_61, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 4.18/1.75  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.18/1.75  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.18/1.75  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.18/1.75  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.18/1.75  tff(f_66, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.18/1.75  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.18/1.75  tff(c_72, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.18/1.75  tff(c_81, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_72])).
% 4.18/1.75  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.18/1.75  tff(c_205, plain, (![A_94, B_95, C_96, D_97]: (k7_relset_1(A_94, B_95, C_96, D_97)=k9_relat_1(C_96, D_97) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.18/1.75  tff(c_212, plain, (![D_97]: (k7_relset_1('#skF_2', '#skF_3', '#skF_5', D_97)=k9_relat_1('#skF_5', D_97))), inference(resolution, [status(thm)], [c_50, c_205])).
% 4.18/1.75  tff(c_48, plain, (r2_hidden('#skF_6', k7_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.18/1.75  tff(c_243, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_48])).
% 4.18/1.75  tff(c_853, plain, (![A_203, B_204, C_205]: (r2_hidden(k4_tarski('#skF_1'(A_203, B_204, C_205), A_203), C_205) | ~r2_hidden(A_203, k9_relat_1(C_205, B_204)) | ~v1_relat_1(C_205))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.18/1.75  tff(c_22, plain, (![C_17, A_15, B_16]: (k1_funct_1(C_17, A_15)=B_16 | ~r2_hidden(k4_tarski(A_15, B_16), C_17) | ~v1_funct_1(C_17) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.18/1.75  tff(c_1167, plain, (![C_262, A_263, B_264]: (k1_funct_1(C_262, '#skF_1'(A_263, B_264, C_262))=A_263 | ~v1_funct_1(C_262) | ~r2_hidden(A_263, k9_relat_1(C_262, B_264)) | ~v1_relat_1(C_262))), inference(resolution, [status(thm)], [c_853, c_22])).
% 4.18/1.75  tff(c_1172, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_243, c_1167])).
% 4.18/1.75  tff(c_1182, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_81, c_54, c_1172])).
% 4.18/1.75  tff(c_14, plain, (![A_9, B_10, C_11]: (r2_hidden('#skF_1'(A_9, B_10, C_11), B_10) | ~r2_hidden(A_9, k9_relat_1(C_11, B_10)) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.18/1.75  tff(c_52, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.18/1.75  tff(c_124, plain, (![A_59, B_60, C_61]: (k1_relset_1(A_59, B_60, C_61)=k1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.18/1.75  tff(c_133, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_124])).
% 4.18/1.75  tff(c_1036, plain, (![B_238, A_239, C_240]: (k1_xboole_0=B_238 | k1_relset_1(A_239, B_238, C_240)=A_239 | ~v1_funct_2(C_240, A_239, B_238) | ~m1_subset_1(C_240, k1_zfmisc_1(k2_zfmisc_1(A_239, B_238))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.18/1.75  tff(c_1043, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_1036])).
% 4.18/1.75  tff(c_1047, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_133, c_1043])).
% 4.18/1.75  tff(c_1048, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_1047])).
% 4.18/1.75  tff(c_18, plain, (![A_9, B_10, C_11]: (r2_hidden('#skF_1'(A_9, B_10, C_11), k1_relat_1(C_11)) | ~r2_hidden(A_9, k9_relat_1(C_11, B_10)) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.18/1.75  tff(c_1056, plain, (![A_9, B_10]: (r2_hidden('#skF_1'(A_9, B_10, '#skF_5'), '#skF_2') | ~r2_hidden(A_9, k9_relat_1('#skF_5', B_10)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1048, c_18])).
% 4.18/1.75  tff(c_1088, plain, (![A_243, B_244]: (r2_hidden('#skF_1'(A_243, B_244, '#skF_5'), '#skF_2') | ~r2_hidden(A_243, k9_relat_1('#skF_5', B_244)))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_1056])).
% 4.18/1.75  tff(c_46, plain, (![F_37]: (k1_funct_1('#skF_5', F_37)!='#skF_6' | ~r2_hidden(F_37, '#skF_4') | ~r2_hidden(F_37, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.18/1.75  tff(c_1199, plain, (![A_265, B_266]: (k1_funct_1('#skF_5', '#skF_1'(A_265, B_266, '#skF_5'))!='#skF_6' | ~r2_hidden('#skF_1'(A_265, B_266, '#skF_5'), '#skF_4') | ~r2_hidden(A_265, k9_relat_1('#skF_5', B_266)))), inference(resolution, [status(thm)], [c_1088, c_46])).
% 4.18/1.75  tff(c_1203, plain, (![A_9]: (k1_funct_1('#skF_5', '#skF_1'(A_9, '#skF_4', '#skF_5'))!='#skF_6' | ~r2_hidden(A_9, k9_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_14, c_1199])).
% 4.18/1.75  tff(c_1207, plain, (![A_267]: (k1_funct_1('#skF_5', '#skF_1'(A_267, '#skF_4', '#skF_5'))!='#skF_6' | ~r2_hidden(A_267, k9_relat_1('#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_1203])).
% 4.18/1.75  tff(c_1214, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_6', '#skF_4', '#skF_5'))!='#skF_6'), inference(resolution, [status(thm)], [c_243, c_1207])).
% 4.18/1.75  tff(c_1227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1182, c_1214])).
% 4.18/1.75  tff(c_1228, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1047])).
% 4.18/1.75  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.18/1.75  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(A_2, k1_zfmisc_1(B_3)) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.18/1.75  tff(c_82, plain, (![A_50, A_51, B_52]: (v1_relat_1(A_50) | ~r1_tarski(A_50, k2_zfmisc_1(A_51, B_52)))), inference(resolution, [status(thm)], [c_6, c_72])).
% 4.18/1.75  tff(c_92, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_82])).
% 4.18/1.75  tff(c_26, plain, (![B_19, A_18]: (~r1_tarski(B_19, A_18) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.18/1.75  tff(c_922, plain, (![C_214, A_215, B_216]: (~r1_tarski(C_214, k4_tarski('#skF_1'(A_215, B_216, C_214), A_215)) | ~r2_hidden(A_215, k9_relat_1(C_214, B_216)) | ~v1_relat_1(C_214))), inference(resolution, [status(thm)], [c_853, c_26])).
% 4.18/1.75  tff(c_926, plain, (![A_215, B_216]: (~r2_hidden(A_215, k9_relat_1(k1_xboole_0, B_216)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_922])).
% 4.18/1.75  tff(c_929, plain, (![A_215, B_216]: (~r2_hidden(A_215, k9_relat_1(k1_xboole_0, B_216)))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_926])).
% 4.18/1.75  tff(c_1236, plain, (![A_215, B_216]: (~r2_hidden(A_215, k9_relat_1('#skF_3', B_216)))), inference(demodulation, [status(thm), theory('equality')], [c_1228, c_929])).
% 4.18/1.75  tff(c_59, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | ~m1_subset_1(A_45, k1_zfmisc_1(B_46)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.18/1.75  tff(c_67, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_59])).
% 4.18/1.75  tff(c_187, plain, (![C_87, A_88]: (k1_xboole_0=C_87 | ~v1_funct_2(C_87, A_88, k1_xboole_0) | k1_xboole_0=A_88 | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_88, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.18/1.75  tff(c_192, plain, (![A_2, A_88]: (k1_xboole_0=A_2 | ~v1_funct_2(A_2, A_88, k1_xboole_0) | k1_xboole_0=A_88 | ~r1_tarski(A_2, k2_zfmisc_1(A_88, k1_xboole_0)))), inference(resolution, [status(thm)], [c_6, c_187])).
% 4.18/1.75  tff(c_1370, plain, (![A_281, A_282]: (A_281='#skF_3' | ~v1_funct_2(A_281, A_282, '#skF_3') | A_282='#skF_3' | ~r1_tarski(A_281, k2_zfmisc_1(A_282, '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1228, c_1228, c_1228, c_1228, c_192])).
% 4.18/1.75  tff(c_1377, plain, ('#skF_5'='#skF_3' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_67, c_1370])).
% 4.18/1.75  tff(c_1382, plain, ('#skF_5'='#skF_3' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1377])).
% 4.18/1.75  tff(c_1383, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_1382])).
% 4.18/1.75  tff(c_1229, plain, (k1_relat_1('#skF_5')!='#skF_2'), inference(splitRight, [status(thm)], [c_1047])).
% 4.18/1.75  tff(c_1384, plain, (k1_relat_1('#skF_5')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1383, c_1229])).
% 4.18/1.75  tff(c_1394, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1383, c_52])).
% 4.18/1.75  tff(c_1390, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1383, c_133])).
% 4.18/1.75  tff(c_1392, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1383, c_67])).
% 4.18/1.75  tff(c_840, plain, (![B_199, C_200]: (k1_relset_1(k1_xboole_0, B_199, C_200)=k1_xboole_0 | ~v1_funct_2(C_200, k1_xboole_0, B_199) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_199))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.18/1.75  tff(c_845, plain, (![B_199, A_2]: (k1_relset_1(k1_xboole_0, B_199, A_2)=k1_xboole_0 | ~v1_funct_2(A_2, k1_xboole_0, B_199) | ~r1_tarski(A_2, k2_zfmisc_1(k1_xboole_0, B_199)))), inference(resolution, [status(thm)], [c_6, c_840])).
% 4.18/1.75  tff(c_1454, plain, (![B_283, A_284]: (k1_relset_1('#skF_3', B_283, A_284)='#skF_3' | ~v1_funct_2(A_284, '#skF_3', B_283) | ~r1_tarski(A_284, k2_zfmisc_1('#skF_3', B_283)))), inference(demodulation, [status(thm), theory('equality')], [c_1228, c_1228, c_1228, c_1228, c_845])).
% 4.18/1.75  tff(c_1457, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_1392, c_1454])).
% 4.18/1.75  tff(c_1464, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1394, c_1390, c_1457])).
% 4.18/1.75  tff(c_1466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1384, c_1464])).
% 4.18/1.75  tff(c_1467, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_1382])).
% 4.18/1.75  tff(c_1472, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1467, c_243])).
% 4.18/1.75  tff(c_1484, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1236, c_1472])).
% 4.18/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.18/1.75  
% 4.18/1.75  Inference rules
% 4.18/1.75  ----------------------
% 4.18/1.75  #Ref     : 0
% 4.18/1.75  #Sup     : 264
% 4.18/1.75  #Fact    : 0
% 4.18/1.75  #Define  : 0
% 4.18/1.75  #Split   : 11
% 4.18/1.75  #Chain   : 0
% 4.18/1.75  #Close   : 0
% 4.18/1.75  
% 4.18/1.75  Ordering : KBO
% 4.18/1.75  
% 4.18/1.75  Simplification rules
% 4.18/1.75  ----------------------
% 4.18/1.75  #Subsume      : 16
% 4.18/1.75  #Demod        : 234
% 4.18/1.75  #Tautology    : 71
% 4.18/1.75  #SimpNegUnit  : 6
% 4.18/1.76  #BackRed      : 95
% 4.18/1.76  
% 4.18/1.76  #Partial instantiations: 0
% 4.18/1.76  #Strategies tried      : 1
% 4.18/1.76  
% 4.18/1.76  Timing (in seconds)
% 4.18/1.76  ----------------------
% 4.18/1.76  Preprocessing        : 0.36
% 4.18/1.76  Parsing              : 0.19
% 4.18/1.76  CNF conversion       : 0.02
% 4.18/1.76  Main loop            : 0.55
% 4.18/1.76  Inferencing          : 0.20
% 4.18/1.76  Reduction            : 0.16
% 4.18/1.76  Demodulation         : 0.12
% 4.18/1.76  BG Simplification    : 0.03
% 4.18/1.76  Subsumption          : 0.11
% 4.18/1.76  Abstraction          : 0.03
% 4.18/1.76  MUC search           : 0.00
% 4.18/1.76  Cooper               : 0.00
% 4.18/1.76  Total                : 0.96
% 4.18/1.76  Index Insertion      : 0.00
% 4.18/1.76  Index Deletion       : 0.00
% 4.18/1.76  Index Matching       : 0.00
% 4.18/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
