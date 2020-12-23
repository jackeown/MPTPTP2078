%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:14 EST 2020

% Result     : Theorem 4.28s
% Output     : CNFRefutation 4.28s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 373 expanded)
%              Number of leaves         :   31 ( 132 expanded)
%              Depth                    :   10
%              Number of atoms          :  236 (1128 expanded)
%              Number of equality atoms :   47 ( 281 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(B,C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_83,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_90,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_94,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_90])).

tff(c_95,plain,(
    ! [C_33,B_34,A_35] :
      ( v5_relat_1(C_33,B_34)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_35,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_99,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_95])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_50,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1070,plain,(
    ! [A_145,C_146,B_147] :
      ( r1_tarski(A_145,C_146)
      | ~ r1_tarski(B_147,C_146)
      | ~ r1_tarski(A_145,B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1098,plain,(
    ! [A_150] :
      ( r1_tarski(A_150,'#skF_3')
      | ~ r1_tarski(A_150,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_50,c_1070])).

tff(c_1111,plain,(
    ! [B_10] :
      ( r1_tarski(k2_relat_1(B_10),'#skF_3')
      | ~ v5_relat_1(B_10,'#skF_2')
      | ~ v1_relat_1(B_10) ) ),
    inference(resolution,[status(thm)],[c_18,c_1098])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_48,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_54,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1224,plain,(
    ! [A_170,B_171,C_172] :
      ( k1_relset_1(A_170,B_171,C_172) = k1_relat_1(C_172)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1228,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1224])).

tff(c_1620,plain,(
    ! [B_225,A_226,C_227] :
      ( k1_xboole_0 = B_225
      | k1_relset_1(A_226,B_225,C_227) = A_226
      | ~ v1_funct_2(C_227,A_226,B_225)
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(A_226,B_225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1626,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_1620])).

tff(c_1630,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1228,c_1626])).

tff(c_1631,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1630])).

tff(c_40,plain,(
    ! [B_24,A_23] :
      ( m1_subset_1(B_24,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_24),A_23)))
      | ~ r1_tarski(k2_relat_1(B_24),A_23)
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1642,plain,(
    ! [A_23] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_23)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_23)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1631,c_40])).

tff(c_1925,plain,(
    ! [A_241] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_241)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_241) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_56,c_1642])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_58,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46])).

tff(c_120,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100,plain,(
    ! [B_36,A_37] :
      ( v5_relat_1(B_36,A_37)
      | ~ r1_tarski(k2_relat_1(B_36),A_37)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_105,plain,(
    ! [B_36] :
      ( v5_relat_1(B_36,k2_relat_1(B_36))
      | ~ v1_relat_1(B_36) ) ),
    inference(resolution,[status(thm)],[c_6,c_100])).

tff(c_122,plain,(
    ! [A_42,C_43,B_44] :
      ( r1_tarski(A_42,C_43)
      | ~ r1_tarski(B_44,C_43)
      | ~ r1_tarski(A_42,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_298,plain,(
    ! [A_73,A_74,B_75] :
      ( r1_tarski(A_73,A_74)
      | ~ r1_tarski(A_73,k2_relat_1(B_75))
      | ~ v5_relat_1(B_75,A_74)
      | ~ v1_relat_1(B_75) ) ),
    inference(resolution,[status(thm)],[c_18,c_122])).

tff(c_750,plain,(
    ! [B_132,A_133,B_134] :
      ( r1_tarski(k2_relat_1(B_132),A_133)
      | ~ v5_relat_1(B_134,A_133)
      | ~ v1_relat_1(B_134)
      | ~ v5_relat_1(B_132,k2_relat_1(B_134))
      | ~ v1_relat_1(B_132) ) ),
    inference(resolution,[status(thm)],[c_18,c_298])).

tff(c_756,plain,(
    ! [B_132] :
      ( r1_tarski(k2_relat_1(B_132),'#skF_2')
      | ~ v1_relat_1('#skF_4')
      | ~ v5_relat_1(B_132,k2_relat_1('#skF_4'))
      | ~ v1_relat_1(B_132) ) ),
    inference(resolution,[status(thm)],[c_99,c_750])).

tff(c_764,plain,(
    ! [B_135] :
      ( r1_tarski(k2_relat_1(B_135),'#skF_2')
      | ~ v5_relat_1(B_135,k2_relat_1('#skF_4'))
      | ~ v1_relat_1(B_135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_756])).

tff(c_768,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_105,c_764])).

tff(c_771,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_768])).

tff(c_134,plain,(
    ! [A_42] :
      ( r1_tarski(A_42,'#skF_3')
      | ~ r1_tarski(A_42,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_50,c_122])).

tff(c_893,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_771,c_134])).

tff(c_249,plain,(
    ! [A_61,B_62,C_63] :
      ( k1_relset_1(A_61,B_62,C_63) = k1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_253,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_249])).

tff(c_772,plain,(
    ! [B_136,A_137,C_138] :
      ( k1_xboole_0 = B_136
      | k1_relset_1(A_137,B_136,C_138) = A_137
      | ~ v1_funct_2(C_138,A_137,B_136)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_137,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_778,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_772])).

tff(c_782,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_253,c_778])).

tff(c_783,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_782])).

tff(c_42,plain,(
    ! [B_24,A_23] :
      ( v1_funct_2(B_24,k1_relat_1(B_24),A_23)
      | ~ r1_tarski(k2_relat_1(B_24),A_23)
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_821,plain,(
    ! [A_23] :
      ( v1_funct_2('#skF_4','#skF_1',A_23)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_23)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_783,c_42])).

tff(c_1040,plain,(
    ! [A_143] :
      ( v1_funct_2('#skF_4','#skF_1',A_143)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_56,c_821])).

tff(c_1043,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_893,c_1040])).

tff(c_1066,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_1043])).

tff(c_1067,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1958,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1925,c_1067])).

tff(c_1967,plain,
    ( ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1111,c_1958])).

tff(c_1977,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_99,c_1967])).

tff(c_1978,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1979,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1985,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1978,c_1979])).

tff(c_1992,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1985,c_52])).

tff(c_1995,plain,(
    ! [C_243,A_244,B_245] :
      ( v1_relat_1(C_243)
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1999,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1992,c_1995])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1980,plain,(
    ! [A_6] : r1_tarski('#skF_1',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1978,c_10])).

tff(c_2372,plain,(
    ! [C_303,B_304,A_305] :
      ( v5_relat_1(C_303,B_304)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(A_305,B_304))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2376,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_1992,c_2372])).

tff(c_2023,plain,(
    ! [B_249,A_250] :
      ( r1_tarski(k2_relat_1(B_249),A_250)
      | ~ v5_relat_1(B_249,A_250)
      | ~ v1_relat_1(B_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2000,plain,(
    ! [B_246,A_247] :
      ( B_246 = A_247
      | ~ r1_tarski(B_246,A_247)
      | ~ r1_tarski(A_247,B_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2005,plain,(
    ! [A_6] :
      ( A_6 = '#skF_1'
      | ~ r1_tarski(A_6,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1980,c_2000])).

tff(c_2030,plain,(
    ! [B_249] :
      ( k2_relat_1(B_249) = '#skF_1'
      | ~ v5_relat_1(B_249,'#skF_1')
      | ~ v1_relat_1(B_249) ) ),
    inference(resolution,[status(thm)],[c_2023,c_2005])).

tff(c_2379,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2376,c_2030])).

tff(c_2382,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1999,c_2379])).

tff(c_2301,plain,(
    ! [C_290,A_291,B_292] :
      ( v4_relat_1(C_290,A_291)
      | ~ m1_subset_1(C_290,k1_zfmisc_1(k2_zfmisc_1(A_291,B_292))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2305,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_1992,c_2301])).

tff(c_2324,plain,(
    ! [B_299,A_300] :
      ( r1_tarski(k1_relat_1(B_299),A_300)
      | ~ v4_relat_1(B_299,A_300)
      | ~ v1_relat_1(B_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2337,plain,(
    ! [B_301] :
      ( k1_relat_1(B_301) = '#skF_1'
      | ~ v4_relat_1(B_301,'#skF_1')
      | ~ v1_relat_1(B_301) ) ),
    inference(resolution,[status(thm)],[c_2324,c_2005])).

tff(c_2340,plain,
    ( k1_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2305,c_2337])).

tff(c_2343,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1999,c_2340])).

tff(c_2834,plain,(
    ! [B_357,A_358] :
      ( m1_subset_1(B_357,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_357),A_358)))
      | ~ r1_tarski(k2_relat_1(B_357),A_358)
      | ~ v1_funct_1(B_357)
      | ~ v1_relat_1(B_357) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2857,plain,(
    ! [A_358] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_358)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_358)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2343,c_2834])).

tff(c_2865,plain,(
    ! [A_358] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_358))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1999,c_56,c_1980,c_2382,c_2857])).

tff(c_2137,plain,(
    ! [C_270,B_271,A_272] :
      ( v5_relat_1(C_270,B_271)
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(A_272,B_271))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2141,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_1992,c_2137])).

tff(c_2144,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2141,c_2030])).

tff(c_2147,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1999,c_2144])).

tff(c_2034,plain,(
    ! [C_252,A_253,B_254] :
      ( v4_relat_1(C_252,A_253)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(A_253,B_254))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2038,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_1992,c_2034])).

tff(c_2082,plain,(
    ! [B_266,A_267] :
      ( r1_tarski(k1_relat_1(B_266),A_267)
      | ~ v4_relat_1(B_266,A_267)
      | ~ v1_relat_1(B_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2102,plain,(
    ! [B_268] :
      ( k1_relat_1(B_268) = '#skF_1'
      | ~ v4_relat_1(B_268,'#skF_1')
      | ~ v1_relat_1(B_268) ) ),
    inference(resolution,[status(thm)],[c_2082,c_2005])).

tff(c_2105,plain,
    ( k1_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2038,c_2102])).

tff(c_2108,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1999,c_2105])).

tff(c_2289,plain,(
    ! [B_288,A_289] :
      ( v1_funct_2(B_288,k1_relat_1(B_288),A_289)
      | ~ r1_tarski(k2_relat_1(B_288),A_289)
      | ~ v1_funct_1(B_288)
      | ~ v1_relat_1(B_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2292,plain,(
    ! [A_289] :
      ( v1_funct_2('#skF_4','#skF_1',A_289)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_289)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2108,c_2289])).

tff(c_2294,plain,(
    ! [A_289] : v1_funct_2('#skF_4','#skF_1',A_289) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1999,c_56,c_1980,c_2147,c_2292])).

tff(c_2033,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_2298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2294,c_2033])).

tff(c_2299,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2869,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2865,c_2299])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:30:30 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.28/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.28/1.75  
% 4.28/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.28/1.75  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.28/1.75  
% 4.28/1.75  %Foreground sorts:
% 4.28/1.75  
% 4.28/1.75  
% 4.28/1.75  %Background operators:
% 4.28/1.75  
% 4.28/1.75  
% 4.28/1.75  %Foreground operators:
% 4.28/1.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.28/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.28/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.28/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.28/1.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.28/1.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.28/1.75  tff('#skF_2', type, '#skF_2': $i).
% 4.28/1.75  tff('#skF_3', type, '#skF_3': $i).
% 4.28/1.75  tff('#skF_1', type, '#skF_1': $i).
% 4.28/1.75  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.28/1.75  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.28/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.28/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.28/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.28/1.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.28/1.75  tff('#skF_4', type, '#skF_4': $i).
% 4.28/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.28/1.75  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.28/1.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.28/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.28/1.75  
% 4.28/1.78  tff(f_115, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 4.28/1.78  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.28/1.78  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.28/1.78  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.28/1.78  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.28/1.78  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.28/1.78  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.28/1.78  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 4.28/1.78  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.28/1.78  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.28/1.78  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.28/1.78  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.28/1.78  tff(c_90, plain, (![C_30, A_31, B_32]: (v1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.28/1.78  tff(c_94, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_90])).
% 4.28/1.78  tff(c_95, plain, (![C_33, B_34, A_35]: (v5_relat_1(C_33, B_34) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_35, B_34))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.28/1.78  tff(c_99, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_95])).
% 4.28/1.78  tff(c_18, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.28/1.78  tff(c_50, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.28/1.78  tff(c_1070, plain, (![A_145, C_146, B_147]: (r1_tarski(A_145, C_146) | ~r1_tarski(B_147, C_146) | ~r1_tarski(A_145, B_147))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.28/1.78  tff(c_1098, plain, (![A_150]: (r1_tarski(A_150, '#skF_3') | ~r1_tarski(A_150, '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_1070])).
% 4.28/1.78  tff(c_1111, plain, (![B_10]: (r1_tarski(k2_relat_1(B_10), '#skF_3') | ~v5_relat_1(B_10, '#skF_2') | ~v1_relat_1(B_10))), inference(resolution, [status(thm)], [c_18, c_1098])).
% 4.28/1.78  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.28/1.78  tff(c_48, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.28/1.78  tff(c_62, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_48])).
% 4.28/1.78  tff(c_54, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.28/1.78  tff(c_1224, plain, (![A_170, B_171, C_172]: (k1_relset_1(A_170, B_171, C_172)=k1_relat_1(C_172) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.28/1.78  tff(c_1228, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_1224])).
% 4.28/1.78  tff(c_1620, plain, (![B_225, A_226, C_227]: (k1_xboole_0=B_225 | k1_relset_1(A_226, B_225, C_227)=A_226 | ~v1_funct_2(C_227, A_226, B_225) | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(A_226, B_225))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.28/1.78  tff(c_1626, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_1620])).
% 4.28/1.78  tff(c_1630, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1228, c_1626])).
% 4.28/1.78  tff(c_1631, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_62, c_1630])).
% 4.28/1.78  tff(c_40, plain, (![B_24, A_23]: (m1_subset_1(B_24, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_24), A_23))) | ~r1_tarski(k2_relat_1(B_24), A_23) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.28/1.78  tff(c_1642, plain, (![A_23]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_23))) | ~r1_tarski(k2_relat_1('#skF_4'), A_23) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1631, c_40])).
% 4.28/1.78  tff(c_1925, plain, (![A_241]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_241))) | ~r1_tarski(k2_relat_1('#skF_4'), A_241))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_56, c_1642])).
% 4.28/1.78  tff(c_46, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.28/1.78  tff(c_58, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46])).
% 4.28/1.78  tff(c_120, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_58])).
% 4.28/1.78  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.28/1.78  tff(c_100, plain, (![B_36, A_37]: (v5_relat_1(B_36, A_37) | ~r1_tarski(k2_relat_1(B_36), A_37) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.28/1.78  tff(c_105, plain, (![B_36]: (v5_relat_1(B_36, k2_relat_1(B_36)) | ~v1_relat_1(B_36))), inference(resolution, [status(thm)], [c_6, c_100])).
% 4.28/1.78  tff(c_122, plain, (![A_42, C_43, B_44]: (r1_tarski(A_42, C_43) | ~r1_tarski(B_44, C_43) | ~r1_tarski(A_42, B_44))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.28/1.78  tff(c_298, plain, (![A_73, A_74, B_75]: (r1_tarski(A_73, A_74) | ~r1_tarski(A_73, k2_relat_1(B_75)) | ~v5_relat_1(B_75, A_74) | ~v1_relat_1(B_75))), inference(resolution, [status(thm)], [c_18, c_122])).
% 4.28/1.78  tff(c_750, plain, (![B_132, A_133, B_134]: (r1_tarski(k2_relat_1(B_132), A_133) | ~v5_relat_1(B_134, A_133) | ~v1_relat_1(B_134) | ~v5_relat_1(B_132, k2_relat_1(B_134)) | ~v1_relat_1(B_132))), inference(resolution, [status(thm)], [c_18, c_298])).
% 4.28/1.78  tff(c_756, plain, (![B_132]: (r1_tarski(k2_relat_1(B_132), '#skF_2') | ~v1_relat_1('#skF_4') | ~v5_relat_1(B_132, k2_relat_1('#skF_4')) | ~v1_relat_1(B_132))), inference(resolution, [status(thm)], [c_99, c_750])).
% 4.28/1.78  tff(c_764, plain, (![B_135]: (r1_tarski(k2_relat_1(B_135), '#skF_2') | ~v5_relat_1(B_135, k2_relat_1('#skF_4')) | ~v1_relat_1(B_135))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_756])).
% 4.28/1.78  tff(c_768, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_105, c_764])).
% 4.28/1.78  tff(c_771, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_768])).
% 4.28/1.78  tff(c_134, plain, (![A_42]: (r1_tarski(A_42, '#skF_3') | ~r1_tarski(A_42, '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_122])).
% 4.28/1.78  tff(c_893, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_771, c_134])).
% 4.28/1.78  tff(c_249, plain, (![A_61, B_62, C_63]: (k1_relset_1(A_61, B_62, C_63)=k1_relat_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.28/1.78  tff(c_253, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_249])).
% 4.28/1.78  tff(c_772, plain, (![B_136, A_137, C_138]: (k1_xboole_0=B_136 | k1_relset_1(A_137, B_136, C_138)=A_137 | ~v1_funct_2(C_138, A_137, B_136) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_137, B_136))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.28/1.78  tff(c_778, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_772])).
% 4.28/1.78  tff(c_782, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_253, c_778])).
% 4.28/1.78  tff(c_783, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_62, c_782])).
% 4.28/1.78  tff(c_42, plain, (![B_24, A_23]: (v1_funct_2(B_24, k1_relat_1(B_24), A_23) | ~r1_tarski(k2_relat_1(B_24), A_23) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.28/1.78  tff(c_821, plain, (![A_23]: (v1_funct_2('#skF_4', '#skF_1', A_23) | ~r1_tarski(k2_relat_1('#skF_4'), A_23) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_783, c_42])).
% 4.28/1.78  tff(c_1040, plain, (![A_143]: (v1_funct_2('#skF_4', '#skF_1', A_143) | ~r1_tarski(k2_relat_1('#skF_4'), A_143))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_56, c_821])).
% 4.28/1.78  tff(c_1043, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_893, c_1040])).
% 4.28/1.78  tff(c_1066, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_1043])).
% 4.28/1.78  tff(c_1067, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_58])).
% 4.28/1.78  tff(c_1958, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_1925, c_1067])).
% 4.28/1.78  tff(c_1967, plain, (~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1111, c_1958])).
% 4.28/1.78  tff(c_1977, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_99, c_1967])).
% 4.28/1.78  tff(c_1978, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_48])).
% 4.28/1.78  tff(c_1979, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_48])).
% 4.28/1.78  tff(c_1985, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1978, c_1979])).
% 4.28/1.78  tff(c_1992, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1985, c_52])).
% 4.28/1.78  tff(c_1995, plain, (![C_243, A_244, B_245]: (v1_relat_1(C_243) | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.28/1.78  tff(c_1999, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1992, c_1995])).
% 4.28/1.78  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.28/1.78  tff(c_1980, plain, (![A_6]: (r1_tarski('#skF_1', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_1978, c_10])).
% 4.28/1.78  tff(c_2372, plain, (![C_303, B_304, A_305]: (v5_relat_1(C_303, B_304) | ~m1_subset_1(C_303, k1_zfmisc_1(k2_zfmisc_1(A_305, B_304))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.28/1.78  tff(c_2376, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_1992, c_2372])).
% 4.28/1.78  tff(c_2023, plain, (![B_249, A_250]: (r1_tarski(k2_relat_1(B_249), A_250) | ~v5_relat_1(B_249, A_250) | ~v1_relat_1(B_249))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.28/1.78  tff(c_2000, plain, (![B_246, A_247]: (B_246=A_247 | ~r1_tarski(B_246, A_247) | ~r1_tarski(A_247, B_246))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.28/1.78  tff(c_2005, plain, (![A_6]: (A_6='#skF_1' | ~r1_tarski(A_6, '#skF_1'))), inference(resolution, [status(thm)], [c_1980, c_2000])).
% 4.28/1.78  tff(c_2030, plain, (![B_249]: (k2_relat_1(B_249)='#skF_1' | ~v5_relat_1(B_249, '#skF_1') | ~v1_relat_1(B_249))), inference(resolution, [status(thm)], [c_2023, c_2005])).
% 4.28/1.78  tff(c_2379, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2376, c_2030])).
% 4.28/1.78  tff(c_2382, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1999, c_2379])).
% 4.28/1.78  tff(c_2301, plain, (![C_290, A_291, B_292]: (v4_relat_1(C_290, A_291) | ~m1_subset_1(C_290, k1_zfmisc_1(k2_zfmisc_1(A_291, B_292))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.28/1.78  tff(c_2305, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_1992, c_2301])).
% 4.28/1.78  tff(c_2324, plain, (![B_299, A_300]: (r1_tarski(k1_relat_1(B_299), A_300) | ~v4_relat_1(B_299, A_300) | ~v1_relat_1(B_299))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.28/1.78  tff(c_2337, plain, (![B_301]: (k1_relat_1(B_301)='#skF_1' | ~v4_relat_1(B_301, '#skF_1') | ~v1_relat_1(B_301))), inference(resolution, [status(thm)], [c_2324, c_2005])).
% 4.28/1.78  tff(c_2340, plain, (k1_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2305, c_2337])).
% 4.28/1.78  tff(c_2343, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1999, c_2340])).
% 4.28/1.78  tff(c_2834, plain, (![B_357, A_358]: (m1_subset_1(B_357, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_357), A_358))) | ~r1_tarski(k2_relat_1(B_357), A_358) | ~v1_funct_1(B_357) | ~v1_relat_1(B_357))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.28/1.78  tff(c_2857, plain, (![A_358]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_358))) | ~r1_tarski(k2_relat_1('#skF_4'), A_358) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2343, c_2834])).
% 4.28/1.78  tff(c_2865, plain, (![A_358]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_358))))), inference(demodulation, [status(thm), theory('equality')], [c_1999, c_56, c_1980, c_2382, c_2857])).
% 4.28/1.78  tff(c_2137, plain, (![C_270, B_271, A_272]: (v5_relat_1(C_270, B_271) | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(A_272, B_271))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.28/1.78  tff(c_2141, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_1992, c_2137])).
% 4.28/1.78  tff(c_2144, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2141, c_2030])).
% 4.28/1.78  tff(c_2147, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1999, c_2144])).
% 4.28/1.78  tff(c_2034, plain, (![C_252, A_253, B_254]: (v4_relat_1(C_252, A_253) | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(A_253, B_254))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.28/1.78  tff(c_2038, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_1992, c_2034])).
% 4.28/1.78  tff(c_2082, plain, (![B_266, A_267]: (r1_tarski(k1_relat_1(B_266), A_267) | ~v4_relat_1(B_266, A_267) | ~v1_relat_1(B_266))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.28/1.78  tff(c_2102, plain, (![B_268]: (k1_relat_1(B_268)='#skF_1' | ~v4_relat_1(B_268, '#skF_1') | ~v1_relat_1(B_268))), inference(resolution, [status(thm)], [c_2082, c_2005])).
% 4.28/1.78  tff(c_2105, plain, (k1_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2038, c_2102])).
% 4.28/1.78  tff(c_2108, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1999, c_2105])).
% 4.28/1.78  tff(c_2289, plain, (![B_288, A_289]: (v1_funct_2(B_288, k1_relat_1(B_288), A_289) | ~r1_tarski(k2_relat_1(B_288), A_289) | ~v1_funct_1(B_288) | ~v1_relat_1(B_288))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.28/1.78  tff(c_2292, plain, (![A_289]: (v1_funct_2('#skF_4', '#skF_1', A_289) | ~r1_tarski(k2_relat_1('#skF_4'), A_289) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2108, c_2289])).
% 4.28/1.78  tff(c_2294, plain, (![A_289]: (v1_funct_2('#skF_4', '#skF_1', A_289))), inference(demodulation, [status(thm), theory('equality')], [c_1999, c_56, c_1980, c_2147, c_2292])).
% 4.28/1.78  tff(c_2033, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_58])).
% 4.28/1.78  tff(c_2298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2294, c_2033])).
% 4.28/1.78  tff(c_2299, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_58])).
% 4.28/1.78  tff(c_2869, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2865, c_2299])).
% 4.28/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.28/1.78  
% 4.28/1.78  Inference rules
% 4.28/1.78  ----------------------
% 4.28/1.78  #Ref     : 0
% 4.28/1.78  #Sup     : 580
% 4.28/1.78  #Fact    : 0
% 4.28/1.78  #Define  : 0
% 4.28/1.78  #Split   : 9
% 4.28/1.78  #Chain   : 0
% 4.28/1.78  #Close   : 0
% 4.28/1.78  
% 4.28/1.78  Ordering : KBO
% 4.28/1.78  
% 4.28/1.78  Simplification rules
% 4.28/1.78  ----------------------
% 4.28/1.78  #Subsume      : 131
% 4.28/1.78  #Demod        : 317
% 4.28/1.78  #Tautology    : 183
% 4.28/1.78  #SimpNegUnit  : 5
% 4.28/1.78  #BackRed      : 8
% 4.28/1.78  
% 4.28/1.78  #Partial instantiations: 0
% 4.28/1.78  #Strategies tried      : 1
% 4.28/1.78  
% 4.28/1.78  Timing (in seconds)
% 4.28/1.78  ----------------------
% 4.28/1.78  Preprocessing        : 0.32
% 4.28/1.78  Parsing              : 0.16
% 4.28/1.78  CNF conversion       : 0.02
% 4.28/1.78  Main loop            : 0.69
% 4.28/1.78  Inferencing          : 0.25
% 4.28/1.78  Reduction            : 0.20
% 4.28/1.78  Demodulation         : 0.14
% 4.28/1.78  BG Simplification    : 0.03
% 4.62/1.78  Subsumption          : 0.15
% 4.62/1.78  Abstraction          : 0.03
% 4.62/1.78  MUC search           : 0.00
% 4.62/1.78  Cooper               : 0.00
% 4.62/1.78  Total                : 1.05
% 4.62/1.78  Index Insertion      : 0.00
% 4.62/1.78  Index Deletion       : 0.00
% 4.62/1.78  Index Matching       : 0.00
% 4.62/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
