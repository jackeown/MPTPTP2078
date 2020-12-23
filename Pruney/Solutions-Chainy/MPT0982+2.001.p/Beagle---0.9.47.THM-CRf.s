%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:55 EST 2020

% Result     : Theorem 10.09s
% Output     : CNFRefutation 10.09s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 267 expanded)
%              Number of leaves         :   41 ( 111 expanded)
%              Depth                    :   16
%              Number of atoms          :  245 ( 925 expanded)
%              Number of equality atoms :   61 ( 245 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_153,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( ( k2_relset_1(A,C,k1_partfun1(A,B,B,C,D,E)) = C
                & v2_funct_1(E) )
             => ( C = k1_xboole_0
                | k2_relset_1(A,B,D) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_119,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_91,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_131,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_109,axiom,(
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

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A)
              & v2_funct_1(A) )
           => r1_tarski(k1_relat_1(A),k2_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_158,plain,(
    ! [A_74,B_75,C_76] :
      ( k2_relset_1(A_74,B_75,C_76) = k2_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_165,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_158])).

tff(c_52,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_167,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_52])).

tff(c_81,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_88,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_81])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_122,plain,(
    ! [C_64,B_65,A_66] :
      ( v5_relat_1(C_64,B_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_66,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_129,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_122])).

tff(c_64,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_754,plain,(
    ! [E_132,B_137,F_135,C_136,A_133,D_134] :
      ( k1_partfun1(A_133,B_137,C_136,D_134,E_132,F_135) = k5_relat_1(E_132,F_135)
      | ~ m1_subset_1(F_135,k1_zfmisc_1(k2_zfmisc_1(C_136,D_134)))
      | ~ v1_funct_1(F_135)
      | ~ m1_subset_1(E_132,k1_zfmisc_1(k2_zfmisc_1(A_133,B_137)))
      | ~ v1_funct_1(E_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_768,plain,(
    ! [A_133,B_137,E_132] :
      ( k1_partfun1(A_133,B_137,'#skF_2','#skF_3',E_132,'#skF_5') = k5_relat_1(E_132,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_132,k1_zfmisc_1(k2_zfmisc_1(A_133,B_137)))
      | ~ v1_funct_1(E_132) ) ),
    inference(resolution,[status(thm)],[c_60,c_754])).

tff(c_1164,plain,(
    ! [A_152,B_153,E_154] :
      ( k1_partfun1(A_152,B_153,'#skF_2','#skF_3',E_154,'#skF_5') = k5_relat_1(E_154,'#skF_5')
      | ~ m1_subset_1(E_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153)))
      | ~ v1_funct_1(E_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_768])).

tff(c_1191,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_1164])).

tff(c_1209,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1191])).

tff(c_58,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_1213,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1209,c_58])).

tff(c_463,plain,(
    ! [D_111,F_115,C_116,E_113,A_114,B_112] :
      ( k4_relset_1(A_114,B_112,C_116,D_111,E_113,F_115) = k5_relat_1(E_113,F_115)
      | ~ m1_subset_1(F_115,k1_zfmisc_1(k2_zfmisc_1(C_116,D_111)))
      | ~ m1_subset_1(E_113,k1_zfmisc_1(k2_zfmisc_1(A_114,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_837,plain,(
    ! [A_139,B_140,E_141] :
      ( k4_relset_1(A_139,B_140,'#skF_2','#skF_3',E_141,'#skF_5') = k5_relat_1(E_141,'#skF_5')
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(resolution,[status(thm)],[c_60,c_463])).

tff(c_868,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_837])).

tff(c_24,plain,(
    ! [A_19,C_21,D_22,B_20,F_24,E_23] :
      ( m1_subset_1(k4_relset_1(A_19,B_20,C_21,D_22,E_23,F_24),k1_zfmisc_1(k2_zfmisc_1(A_19,D_22)))
      | ~ m1_subset_1(F_24,k1_zfmisc_1(k2_zfmisc_1(C_21,D_22)))
      | ~ m1_subset_1(E_23,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_905,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_868,c_24])).

tff(c_909,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_60,c_905])).

tff(c_28,plain,(
    ! [A_28,B_29,C_30] :
      ( k2_relset_1(A_28,B_29,C_30) = k2_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_955,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_909,c_28])).

tff(c_1239,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1213,c_955])).

tff(c_89,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_81])).

tff(c_130,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_122])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ! [B_47,A_46] :
      ( m1_subset_1(B_47,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_47),A_46)))
      | ~ r1_tarski(k2_relat_1(B_47),A_46)
      | ~ v1_funct_1(B_47)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1692,plain,(
    ! [B_199,A_200,A_198,B_197,E_196] :
      ( k4_relset_1(A_198,B_199,k1_relat_1(B_197),A_200,E_196,B_197) = k5_relat_1(E_196,B_197)
      | ~ m1_subset_1(E_196,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199)))
      | ~ r1_tarski(k2_relat_1(B_197),A_200)
      | ~ v1_funct_1(B_197)
      | ~ v1_relat_1(B_197) ) ),
    inference(resolution,[status(thm)],[c_46,c_463])).

tff(c_1927,plain,(
    ! [B_226,A_227] :
      ( k4_relset_1('#skF_1','#skF_2',k1_relat_1(B_226),A_227,'#skF_4',B_226) = k5_relat_1('#skF_4',B_226)
      | ~ r1_tarski(k2_relat_1(B_226),A_227)
      | ~ v1_funct_1(B_226)
      | ~ v1_relat_1(B_226) ) ),
    inference(resolution,[status(thm)],[c_66,c_1692])).

tff(c_4443,plain,(
    ! [B_365] :
      ( k4_relset_1('#skF_1','#skF_2',k1_relat_1(B_365),k2_relat_1(B_365),'#skF_4',B_365) = k5_relat_1('#skF_4',B_365)
      | ~ v1_funct_1(B_365)
      | ~ v1_relat_1(B_365) ) ),
    inference(resolution,[status(thm)],[c_6,c_1927])).

tff(c_599,plain,(
    ! [E_127,C_126,F_130,D_131,A_129,B_128] :
      ( m1_subset_1(k4_relset_1(A_129,B_128,C_126,D_131,E_127,F_130),k1_zfmisc_1(k2_zfmisc_1(A_129,D_131)))
      | ~ m1_subset_1(F_130,k1_zfmisc_1(k2_zfmisc_1(C_126,D_131)))
      | ~ m1_subset_1(E_127,k1_zfmisc_1(k2_zfmisc_1(A_129,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    ! [C_18,B_17,A_16] :
      ( v5_relat_1(C_18,B_17)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1526,plain,(
    ! [C_182,F_181,D_179,B_178,A_180,E_183] :
      ( v5_relat_1(k4_relset_1(A_180,B_178,C_182,D_179,E_183,F_181),D_179)
      | ~ m1_subset_1(F_181,k1_zfmisc_1(k2_zfmisc_1(C_182,D_179)))
      | ~ m1_subset_1(E_183,k1_zfmisc_1(k2_zfmisc_1(A_180,B_178))) ) ),
    inference(resolution,[status(thm)],[c_599,c_20])).

tff(c_1554,plain,(
    ! [A_46,B_47,B_178,A_180,E_183] :
      ( v5_relat_1(k4_relset_1(A_180,B_178,k1_relat_1(B_47),A_46,E_183,B_47),A_46)
      | ~ m1_subset_1(E_183,k1_zfmisc_1(k2_zfmisc_1(A_180,B_178)))
      | ~ r1_tarski(k2_relat_1(B_47),A_46)
      | ~ v1_funct_1(B_47)
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_46,c_1526])).

tff(c_4449,plain,(
    ! [B_365] :
      ( v5_relat_1(k5_relat_1('#skF_4',B_365),k2_relat_1(B_365))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ r1_tarski(k2_relat_1(B_365),k2_relat_1(B_365))
      | ~ v1_funct_1(B_365)
      | ~ v1_relat_1(B_365)
      | ~ v1_funct_1(B_365)
      | ~ v1_relat_1(B_365) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4443,c_1554])).

tff(c_4491,plain,(
    ! [B_367] :
      ( v5_relat_1(k5_relat_1('#skF_4',B_367),k2_relat_1(B_367))
      | ~ v1_funct_1(B_367)
      | ~ v1_relat_1(B_367) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_66,c_4449])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_941,plain,
    ( v1_relat_1(k5_relat_1('#skF_4','#skF_5'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_909,c_8])).

tff(c_961,plain,(
    v1_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_941])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_110,plain,(
    ! [B_62,A_63] :
      ( r1_tarski(k2_relat_1(B_62),A_63)
      | ~ v5_relat_1(B_62,A_63)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_176,plain,(
    ! [B_77,A_78] :
      ( k2_relat_1(B_77) = A_78
      | ~ r1_tarski(A_78,k2_relat_1(B_77))
      | ~ v5_relat_1(B_77,A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(resolution,[status(thm)],[c_110,c_2])).

tff(c_3203,plain,(
    ! [B_320,B_319] :
      ( k2_relat_1(B_320) = k2_relat_1(B_319)
      | ~ v5_relat_1(B_319,k2_relat_1(B_320))
      | ~ v1_relat_1(B_319)
      | ~ v5_relat_1(B_320,k2_relat_1(B_319))
      | ~ v1_relat_1(B_320) ) ),
    inference(resolution,[status(thm)],[c_12,c_176])).

tff(c_3208,plain,(
    ! [B_319] :
      ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(B_319)
      | ~ v5_relat_1(B_319,'#skF_3')
      | ~ v1_relat_1(B_319)
      | ~ v5_relat_1(k5_relat_1('#skF_4','#skF_5'),k2_relat_1(B_319))
      | ~ v1_relat_1(k5_relat_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1239,c_3203])).

tff(c_3219,plain,(
    ! [B_319] :
      ( k2_relat_1(B_319) = '#skF_3'
      | ~ v5_relat_1(B_319,'#skF_3')
      | ~ v1_relat_1(B_319)
      | ~ v5_relat_1(k5_relat_1('#skF_4','#skF_5'),k2_relat_1(B_319)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_961,c_1239,c_3208])).

tff(c_4495,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4491,c_3219])).

tff(c_4511,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_64,c_130,c_4495])).

tff(c_56,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_62,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_141,plain,(
    ! [A_71,B_72,C_73] :
      ( k1_relset_1(A_71,B_72,C_73) = k1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_149,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_141])).

tff(c_305,plain,(
    ! [B_103,A_104,C_105] :
      ( k1_xboole_0 = B_103
      | k1_relset_1(A_104,B_103,C_105) = A_104
      | ~ v1_funct_2(C_105,A_104,B_103)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_104,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_314,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_305])).

tff(c_321,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_149,c_314])).

tff(c_322,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_321])).

tff(c_402,plain,(
    ! [A_106,B_107] :
      ( r1_tarski(k1_relat_1(A_106),k2_relat_1(B_107))
      | ~ v2_funct_1(A_106)
      | k2_relat_1(k5_relat_1(B_107,A_106)) != k2_relat_1(A_106)
      | ~ v1_funct_1(B_107)
      | ~ v1_relat_1(B_107)
      | ~ v1_funct_1(A_106)
      | ~ v1_relat_1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_413,plain,(
    ! [B_107] :
      ( r1_tarski('#skF_2',k2_relat_1(B_107))
      | ~ v2_funct_1('#skF_5')
      | k2_relat_1(k5_relat_1(B_107,'#skF_5')) != k2_relat_1('#skF_5')
      | ~ v1_funct_1(B_107)
      | ~ v1_relat_1(B_107)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_402])).

tff(c_419,plain,(
    ! [B_107] :
      ( r1_tarski('#skF_2',k2_relat_1(B_107))
      | k2_relat_1(k5_relat_1(B_107,'#skF_5')) != k2_relat_1('#skF_5')
      | ~ v1_funct_1(B_107)
      | ~ v1_relat_1(B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_64,c_56,c_413])).

tff(c_5514,plain,(
    ! [B_435] :
      ( r1_tarski('#skF_2',k2_relat_1(B_435))
      | k2_relat_1(k5_relat_1(B_435,'#skF_5')) != '#skF_3'
      | ~ v1_funct_1(B_435)
      | ~ v1_relat_1(B_435) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4511,c_419])).

tff(c_117,plain,(
    ! [B_62,A_63] :
      ( k2_relat_1(B_62) = A_63
      | ~ r1_tarski(A_63,k2_relat_1(B_62))
      | ~ v5_relat_1(B_62,A_63)
      | ~ v1_relat_1(B_62) ) ),
    inference(resolution,[status(thm)],[c_110,c_2])).

tff(c_7915,plain,(
    ! [B_564] :
      ( k2_relat_1(B_564) = '#skF_2'
      | ~ v5_relat_1(B_564,'#skF_2')
      | k2_relat_1(k5_relat_1(B_564,'#skF_5')) != '#skF_3'
      | ~ v1_funct_1(B_564)
      | ~ v1_relat_1(B_564) ) ),
    inference(resolution,[status(thm)],[c_5514,c_117])).

tff(c_7918,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1239,c_7915])).

tff(c_7921,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_70,c_129,c_7918])).

tff(c_7923,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_7921])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:55:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.09/3.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.09/3.83  
% 10.09/3.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.09/3.83  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.09/3.83  
% 10.09/3.83  %Foreground sorts:
% 10.09/3.83  
% 10.09/3.83  
% 10.09/3.83  %Background operators:
% 10.09/3.83  
% 10.09/3.83  
% 10.09/3.83  %Foreground operators:
% 10.09/3.83  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.09/3.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.09/3.83  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.09/3.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.09/3.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.09/3.83  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.09/3.83  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.09/3.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.09/3.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.09/3.83  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.09/3.83  tff('#skF_5', type, '#skF_5': $i).
% 10.09/3.83  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.09/3.83  tff('#skF_2', type, '#skF_2': $i).
% 10.09/3.83  tff('#skF_3', type, '#skF_3': $i).
% 10.09/3.83  tff('#skF_1', type, '#skF_1': $i).
% 10.09/3.83  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.09/3.83  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.09/3.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.09/3.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.09/3.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.09/3.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.09/3.83  tff('#skF_4', type, '#skF_4': $i).
% 10.09/3.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.09/3.83  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.09/3.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.09/3.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.09/3.83  
% 10.09/3.85  tff(f_153, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_funct_2)).
% 10.09/3.85  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.09/3.85  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.09/3.85  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.09/3.85  tff(f_119, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 10.09/3.85  tff(f_91, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 10.09/3.85  tff(f_77, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 10.09/3.85  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.09/3.85  tff(f_131, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 10.09/3.85  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.09/3.85  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 10.09/3.85  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 10.09/3.85  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.09/3.85  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 10.09/3.85  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A)) & v2_funct_1(A)) => r1_tarski(k1_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_funct_1)).
% 10.09/3.85  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 10.09/3.85  tff(c_158, plain, (![A_74, B_75, C_76]: (k2_relset_1(A_74, B_75, C_76)=k2_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.09/3.85  tff(c_165, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_158])).
% 10.09/3.85  tff(c_52, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_153])).
% 10.09/3.85  tff(c_167, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_52])).
% 10.09/3.85  tff(c_81, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.09/3.85  tff(c_88, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_81])).
% 10.09/3.85  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 10.09/3.85  tff(c_122, plain, (![C_64, B_65, A_66]: (v5_relat_1(C_64, B_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_66, B_65))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.09/3.85  tff(c_129, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_122])).
% 10.09/3.85  tff(c_64, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_153])).
% 10.09/3.85  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 10.09/3.85  tff(c_754, plain, (![E_132, B_137, F_135, C_136, A_133, D_134]: (k1_partfun1(A_133, B_137, C_136, D_134, E_132, F_135)=k5_relat_1(E_132, F_135) | ~m1_subset_1(F_135, k1_zfmisc_1(k2_zfmisc_1(C_136, D_134))) | ~v1_funct_1(F_135) | ~m1_subset_1(E_132, k1_zfmisc_1(k2_zfmisc_1(A_133, B_137))) | ~v1_funct_1(E_132))), inference(cnfTransformation, [status(thm)], [f_119])).
% 10.09/3.85  tff(c_768, plain, (![A_133, B_137, E_132]: (k1_partfun1(A_133, B_137, '#skF_2', '#skF_3', E_132, '#skF_5')=k5_relat_1(E_132, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_132, k1_zfmisc_1(k2_zfmisc_1(A_133, B_137))) | ~v1_funct_1(E_132))), inference(resolution, [status(thm)], [c_60, c_754])).
% 10.09/3.85  tff(c_1164, plain, (![A_152, B_153, E_154]: (k1_partfun1(A_152, B_153, '#skF_2', '#skF_3', E_154, '#skF_5')=k5_relat_1(E_154, '#skF_5') | ~m1_subset_1(E_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))) | ~v1_funct_1(E_154))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_768])).
% 10.09/3.85  tff(c_1191, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_1164])).
% 10.09/3.85  tff(c_1209, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1191])).
% 10.09/3.85  tff(c_58, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_153])).
% 10.09/3.85  tff(c_1213, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1209, c_58])).
% 10.09/3.85  tff(c_463, plain, (![D_111, F_115, C_116, E_113, A_114, B_112]: (k4_relset_1(A_114, B_112, C_116, D_111, E_113, F_115)=k5_relat_1(E_113, F_115) | ~m1_subset_1(F_115, k1_zfmisc_1(k2_zfmisc_1(C_116, D_111))) | ~m1_subset_1(E_113, k1_zfmisc_1(k2_zfmisc_1(A_114, B_112))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.09/3.85  tff(c_837, plain, (![A_139, B_140, E_141]: (k4_relset_1(A_139, B_140, '#skF_2', '#skF_3', E_141, '#skF_5')=k5_relat_1(E_141, '#skF_5') | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(resolution, [status(thm)], [c_60, c_463])).
% 10.09/3.85  tff(c_868, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_837])).
% 10.09/3.85  tff(c_24, plain, (![A_19, C_21, D_22, B_20, F_24, E_23]: (m1_subset_1(k4_relset_1(A_19, B_20, C_21, D_22, E_23, F_24), k1_zfmisc_1(k2_zfmisc_1(A_19, D_22))) | ~m1_subset_1(F_24, k1_zfmisc_1(k2_zfmisc_1(C_21, D_22))) | ~m1_subset_1(E_23, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.09/3.85  tff(c_905, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_868, c_24])).
% 10.09/3.85  tff(c_909, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_60, c_905])).
% 10.09/3.85  tff(c_28, plain, (![A_28, B_29, C_30]: (k2_relset_1(A_28, B_29, C_30)=k2_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.09/3.85  tff(c_955, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_909, c_28])).
% 10.09/3.85  tff(c_1239, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1213, c_955])).
% 10.09/3.85  tff(c_89, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_81])).
% 10.09/3.85  tff(c_130, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_122])).
% 10.09/3.85  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.09/3.85  tff(c_46, plain, (![B_47, A_46]: (m1_subset_1(B_47, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_47), A_46))) | ~r1_tarski(k2_relat_1(B_47), A_46) | ~v1_funct_1(B_47) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_131])).
% 10.09/3.85  tff(c_1692, plain, (![B_199, A_200, A_198, B_197, E_196]: (k4_relset_1(A_198, B_199, k1_relat_1(B_197), A_200, E_196, B_197)=k5_relat_1(E_196, B_197) | ~m1_subset_1(E_196, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))) | ~r1_tarski(k2_relat_1(B_197), A_200) | ~v1_funct_1(B_197) | ~v1_relat_1(B_197))), inference(resolution, [status(thm)], [c_46, c_463])).
% 10.09/3.85  tff(c_1927, plain, (![B_226, A_227]: (k4_relset_1('#skF_1', '#skF_2', k1_relat_1(B_226), A_227, '#skF_4', B_226)=k5_relat_1('#skF_4', B_226) | ~r1_tarski(k2_relat_1(B_226), A_227) | ~v1_funct_1(B_226) | ~v1_relat_1(B_226))), inference(resolution, [status(thm)], [c_66, c_1692])).
% 10.09/3.85  tff(c_4443, plain, (![B_365]: (k4_relset_1('#skF_1', '#skF_2', k1_relat_1(B_365), k2_relat_1(B_365), '#skF_4', B_365)=k5_relat_1('#skF_4', B_365) | ~v1_funct_1(B_365) | ~v1_relat_1(B_365))), inference(resolution, [status(thm)], [c_6, c_1927])).
% 10.09/3.85  tff(c_599, plain, (![E_127, C_126, F_130, D_131, A_129, B_128]: (m1_subset_1(k4_relset_1(A_129, B_128, C_126, D_131, E_127, F_130), k1_zfmisc_1(k2_zfmisc_1(A_129, D_131))) | ~m1_subset_1(F_130, k1_zfmisc_1(k2_zfmisc_1(C_126, D_131))) | ~m1_subset_1(E_127, k1_zfmisc_1(k2_zfmisc_1(A_129, B_128))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.09/3.85  tff(c_20, plain, (![C_18, B_17, A_16]: (v5_relat_1(C_18, B_17) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.09/3.85  tff(c_1526, plain, (![C_182, F_181, D_179, B_178, A_180, E_183]: (v5_relat_1(k4_relset_1(A_180, B_178, C_182, D_179, E_183, F_181), D_179) | ~m1_subset_1(F_181, k1_zfmisc_1(k2_zfmisc_1(C_182, D_179))) | ~m1_subset_1(E_183, k1_zfmisc_1(k2_zfmisc_1(A_180, B_178))))), inference(resolution, [status(thm)], [c_599, c_20])).
% 10.09/3.85  tff(c_1554, plain, (![A_46, B_47, B_178, A_180, E_183]: (v5_relat_1(k4_relset_1(A_180, B_178, k1_relat_1(B_47), A_46, E_183, B_47), A_46) | ~m1_subset_1(E_183, k1_zfmisc_1(k2_zfmisc_1(A_180, B_178))) | ~r1_tarski(k2_relat_1(B_47), A_46) | ~v1_funct_1(B_47) | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_46, c_1526])).
% 10.09/3.85  tff(c_4449, plain, (![B_365]: (v5_relat_1(k5_relat_1('#skF_4', B_365), k2_relat_1(B_365)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~r1_tarski(k2_relat_1(B_365), k2_relat_1(B_365)) | ~v1_funct_1(B_365) | ~v1_relat_1(B_365) | ~v1_funct_1(B_365) | ~v1_relat_1(B_365))), inference(superposition, [status(thm), theory('equality')], [c_4443, c_1554])).
% 10.09/3.85  tff(c_4491, plain, (![B_367]: (v5_relat_1(k5_relat_1('#skF_4', B_367), k2_relat_1(B_367)) | ~v1_funct_1(B_367) | ~v1_relat_1(B_367))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_66, c_4449])).
% 10.09/3.85  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.09/3.85  tff(c_8, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.09/3.85  tff(c_941, plain, (v1_relat_1(k5_relat_1('#skF_4', '#skF_5')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_909, c_8])).
% 10.09/3.85  tff(c_961, plain, (v1_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_941])).
% 10.09/3.85  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.09/3.85  tff(c_110, plain, (![B_62, A_63]: (r1_tarski(k2_relat_1(B_62), A_63) | ~v5_relat_1(B_62, A_63) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.09/3.85  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.09/3.85  tff(c_176, plain, (![B_77, A_78]: (k2_relat_1(B_77)=A_78 | ~r1_tarski(A_78, k2_relat_1(B_77)) | ~v5_relat_1(B_77, A_78) | ~v1_relat_1(B_77))), inference(resolution, [status(thm)], [c_110, c_2])).
% 10.09/3.85  tff(c_3203, plain, (![B_320, B_319]: (k2_relat_1(B_320)=k2_relat_1(B_319) | ~v5_relat_1(B_319, k2_relat_1(B_320)) | ~v1_relat_1(B_319) | ~v5_relat_1(B_320, k2_relat_1(B_319)) | ~v1_relat_1(B_320))), inference(resolution, [status(thm)], [c_12, c_176])).
% 10.09/3.85  tff(c_3208, plain, (![B_319]: (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(B_319) | ~v5_relat_1(B_319, '#skF_3') | ~v1_relat_1(B_319) | ~v5_relat_1(k5_relat_1('#skF_4', '#skF_5'), k2_relat_1(B_319)) | ~v1_relat_1(k5_relat_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1239, c_3203])).
% 10.09/3.85  tff(c_3219, plain, (![B_319]: (k2_relat_1(B_319)='#skF_3' | ~v5_relat_1(B_319, '#skF_3') | ~v1_relat_1(B_319) | ~v5_relat_1(k5_relat_1('#skF_4', '#skF_5'), k2_relat_1(B_319)))), inference(demodulation, [status(thm), theory('equality')], [c_961, c_1239, c_3208])).
% 10.09/3.85  tff(c_4495, plain, (k2_relat_1('#skF_5')='#skF_3' | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_4491, c_3219])).
% 10.09/3.85  tff(c_4511, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_89, c_64, c_130, c_4495])).
% 10.09/3.85  tff(c_56, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_153])).
% 10.09/3.85  tff(c_54, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_153])).
% 10.09/3.85  tff(c_62, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_153])).
% 10.09/3.85  tff(c_141, plain, (![A_71, B_72, C_73]: (k1_relset_1(A_71, B_72, C_73)=k1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.09/3.85  tff(c_149, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_141])).
% 10.09/3.85  tff(c_305, plain, (![B_103, A_104, C_105]: (k1_xboole_0=B_103 | k1_relset_1(A_104, B_103, C_105)=A_104 | ~v1_funct_2(C_105, A_104, B_103) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_104, B_103))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 10.09/3.85  tff(c_314, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_305])).
% 10.09/3.85  tff(c_321, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_149, c_314])).
% 10.09/3.85  tff(c_322, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_54, c_321])).
% 10.09/3.85  tff(c_402, plain, (![A_106, B_107]: (r1_tarski(k1_relat_1(A_106), k2_relat_1(B_107)) | ~v2_funct_1(A_106) | k2_relat_1(k5_relat_1(B_107, A_106))!=k2_relat_1(A_106) | ~v1_funct_1(B_107) | ~v1_relat_1(B_107) | ~v1_funct_1(A_106) | ~v1_relat_1(A_106))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.09/3.85  tff(c_413, plain, (![B_107]: (r1_tarski('#skF_2', k2_relat_1(B_107)) | ~v2_funct_1('#skF_5') | k2_relat_1(k5_relat_1(B_107, '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1(B_107) | ~v1_relat_1(B_107) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_322, c_402])).
% 10.09/3.85  tff(c_419, plain, (![B_107]: (r1_tarski('#skF_2', k2_relat_1(B_107)) | k2_relat_1(k5_relat_1(B_107, '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1(B_107) | ~v1_relat_1(B_107))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_64, c_56, c_413])).
% 10.09/3.85  tff(c_5514, plain, (![B_435]: (r1_tarski('#skF_2', k2_relat_1(B_435)) | k2_relat_1(k5_relat_1(B_435, '#skF_5'))!='#skF_3' | ~v1_funct_1(B_435) | ~v1_relat_1(B_435))), inference(demodulation, [status(thm), theory('equality')], [c_4511, c_419])).
% 10.09/3.85  tff(c_117, plain, (![B_62, A_63]: (k2_relat_1(B_62)=A_63 | ~r1_tarski(A_63, k2_relat_1(B_62)) | ~v5_relat_1(B_62, A_63) | ~v1_relat_1(B_62))), inference(resolution, [status(thm)], [c_110, c_2])).
% 10.09/3.85  tff(c_7915, plain, (![B_564]: (k2_relat_1(B_564)='#skF_2' | ~v5_relat_1(B_564, '#skF_2') | k2_relat_1(k5_relat_1(B_564, '#skF_5'))!='#skF_3' | ~v1_funct_1(B_564) | ~v1_relat_1(B_564))), inference(resolution, [status(thm)], [c_5514, c_117])).
% 10.09/3.85  tff(c_7918, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1239, c_7915])).
% 10.09/3.85  tff(c_7921, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_70, c_129, c_7918])).
% 10.09/3.85  tff(c_7923, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_7921])).
% 10.09/3.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.09/3.85  
% 10.09/3.85  Inference rules
% 10.09/3.85  ----------------------
% 10.09/3.85  #Ref     : 0
% 10.09/3.85  #Sup     : 2000
% 10.09/3.85  #Fact    : 0
% 10.09/3.85  #Define  : 0
% 10.09/3.85  #Split   : 22
% 10.09/3.85  #Chain   : 0
% 10.09/3.85  #Close   : 0
% 10.09/3.85  
% 10.09/3.85  Ordering : KBO
% 10.09/3.85  
% 10.09/3.85  Simplification rules
% 10.09/3.85  ----------------------
% 10.09/3.85  #Subsume      : 88
% 10.09/3.85  #Demod        : 1344
% 10.09/3.85  #Tautology    : 423
% 10.09/3.85  #SimpNegUnit  : 69
% 10.09/3.85  #BackRed      : 95
% 10.09/3.85  
% 10.09/3.85  #Partial instantiations: 0
% 10.09/3.85  #Strategies tried      : 1
% 10.09/3.85  
% 10.09/3.85  Timing (in seconds)
% 10.09/3.85  ----------------------
% 10.09/3.86  Preprocessing        : 0.35
% 10.09/3.86  Parsing              : 0.19
% 10.09/3.86  CNF conversion       : 0.02
% 10.09/3.86  Main loop            : 2.74
% 10.09/3.86  Inferencing          : 0.76
% 10.09/3.86  Reduction            : 1.13
% 10.09/3.86  Demodulation         : 0.85
% 10.09/3.86  BG Simplification    : 0.07
% 10.09/3.86  Subsumption          : 0.56
% 10.09/3.86  Abstraction          : 0.10
% 10.09/3.86  MUC search           : 0.00
% 10.09/3.86  Cooper               : 0.00
% 10.09/3.86  Total                : 3.13
% 10.09/3.86  Index Insertion      : 0.00
% 10.09/3.86  Index Deletion       : 0.00
% 10.09/3.86  Index Matching       : 0.00
% 10.09/3.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
