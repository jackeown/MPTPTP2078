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
% DateTime   : Thu Dec  3 10:11:14 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 397 expanded)
%              Number of leaves         :   34 ( 142 expanded)
%              Depth                    :   10
%              Number of atoms          :  261 (1198 expanded)
%              Number of equality atoms :   47 ( 289 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_133,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v5_relat_1(C,A) )
         => v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t218_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_101,axiom,(
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

tff(f_113,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_928,plain,(
    ! [C_144,A_145,B_146] :
      ( v1_relat_1(C_144)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_932,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_928])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_980,plain,(
    ! [C_162,B_163,A_164] :
      ( v5_relat_1(C_162,B_163)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_164,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_984,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_980])).

tff(c_985,plain,(
    ! [C_165,B_166,A_167] :
      ( v5_relat_1(C_165,B_166)
      | ~ v5_relat_1(C_165,A_167)
      | ~ v1_relat_1(C_165)
      | ~ r1_tarski(A_167,B_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_987,plain,(
    ! [B_166] :
      ( v5_relat_1('#skF_4',B_166)
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_2',B_166) ) ),
    inference(resolution,[status(thm)],[c_984,c_985])).

tff(c_994,plain,(
    ! [B_168] :
      ( v5_relat_1('#skF_4',B_168)
      | ~ r1_tarski('#skF_2',B_168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_932,c_987])).

tff(c_18,plain,(
    ! [C_11,B_9,A_8] :
      ( v5_relat_1(C_11,B_9)
      | ~ v5_relat_1(C_11,A_8)
      | ~ v1_relat_1(C_11)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_996,plain,(
    ! [B_9,B_168] :
      ( v5_relat_1('#skF_4',B_9)
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski(B_168,B_9)
      | ~ r1_tarski('#skF_2',B_168) ) ),
    inference(resolution,[status(thm)],[c_994,c_18])).

tff(c_1009,plain,(
    ! [B_170,B_171] :
      ( v5_relat_1('#skF_4',B_170)
      | ~ r1_tarski(B_171,B_170)
      | ~ r1_tarski('#skF_2',B_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_932,c_996])).

tff(c_1019,plain,
    ( v5_relat_1('#skF_4','#skF_3')
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_1009])).

tff(c_1026,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1019])).

tff(c_16,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1063,plain,(
    ! [A_175,B_176,C_177] :
      ( k1_relset_1(A_175,B_176,C_177) = k1_relat_1(C_177)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1067,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_1063])).

tff(c_1211,plain,(
    ! [B_215,A_216,C_217] :
      ( k1_xboole_0 = B_215
      | k1_relset_1(A_216,B_215,C_217) = A_216
      | ~ v1_funct_2(C_217,A_216,B_215)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_216,B_215))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1217,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_1211])).

tff(c_1221,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1067,c_1217])).

tff(c_1222,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1221])).

tff(c_48,plain,(
    ! [B_32,A_31] :
      ( m1_subset_1(B_32,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_32),A_31)))
      | ~ r1_tarski(k2_relat_1(B_32),A_31)
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1204,plain,(
    ! [D_211,B_212,C_213,A_214] :
      ( m1_subset_1(D_211,k1_zfmisc_1(k2_zfmisc_1(B_212,C_213)))
      | ~ r1_tarski(k1_relat_1(D_211),B_212)
      | ~ m1_subset_1(D_211,k1_zfmisc_1(k2_zfmisc_1(A_214,C_213))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1485,plain,(
    ! [B_232,B_233,A_234] :
      ( m1_subset_1(B_232,k1_zfmisc_1(k2_zfmisc_1(B_233,A_234)))
      | ~ r1_tarski(k1_relat_1(B_232),B_233)
      | ~ r1_tarski(k2_relat_1(B_232),A_234)
      | ~ v1_funct_1(B_232)
      | ~ v1_relat_1(B_232) ) ),
    inference(resolution,[status(thm)],[c_48,c_1204])).

tff(c_103,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_107,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_103])).

tff(c_115,plain,(
    ! [C_44,B_45,A_46] :
      ( v5_relat_1(C_44,B_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_46,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_119,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_115])).

tff(c_160,plain,(
    ! [C_59,B_60,A_61] :
      ( v5_relat_1(C_59,B_60)
      | ~ v5_relat_1(C_59,A_61)
      | ~ v1_relat_1(C_59)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_164,plain,(
    ! [B_60] :
      ( v5_relat_1('#skF_4',B_60)
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_2',B_60) ) ),
    inference(resolution,[status(thm)],[c_119,c_160])).

tff(c_169,plain,(
    ! [B_62] :
      ( v5_relat_1('#skF_4',B_62)
      | ~ r1_tarski('#skF_2',B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_164])).

tff(c_171,plain,(
    ! [B_9,B_62] :
      ( v5_relat_1('#skF_4',B_9)
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski(B_62,B_9)
      | ~ r1_tarski('#skF_2',B_62) ) ),
    inference(resolution,[status(thm)],[c_169,c_18])).

tff(c_183,plain,(
    ! [B_63,B_64] :
      ( v5_relat_1('#skF_4',B_63)
      | ~ r1_tarski(B_64,B_63)
      | ~ r1_tarski('#skF_2',B_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_171])).

tff(c_193,plain,
    ( v5_relat_1('#skF_4','#skF_3')
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_183])).

tff(c_200,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_193])).

tff(c_238,plain,(
    ! [A_69,B_70,C_71] :
      ( k1_relset_1(A_69,B_70,C_71) = k1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_242,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_238])).

tff(c_631,plain,(
    ! [B_130,A_131,C_132] :
      ( k1_xboole_0 = B_130
      | k1_relset_1(A_131,B_130,C_132) = A_131
      | ~ v1_funct_2(C_132,A_131,B_130)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_131,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_640,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_631])).

tff(c_647,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_242,c_640])).

tff(c_648,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_647])).

tff(c_50,plain,(
    ! [B_32,A_31] :
      ( v1_funct_2(B_32,k1_relat_1(B_32),A_31)
      | ~ r1_tarski(k2_relat_1(B_32),A_31)
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_682,plain,(
    ! [A_31] :
      ( v1_funct_2('#skF_4','#skF_1',A_31)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_31)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_648,c_50])).

tff(c_871,plain,(
    ! [A_139] :
      ( v1_funct_2('#skF_4','#skF_1',A_139)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_64,c_682])).

tff(c_875,plain,(
    ! [A_6] :
      ( v1_funct_2('#skF_4','#skF_1',A_6)
      | ~ v5_relat_1('#skF_4',A_6)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_871])).

tff(c_884,plain,(
    ! [A_140] :
      ( v1_funct_2('#skF_4','#skF_1',A_140)
      | ~ v5_relat_1('#skF_4',A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_875])).

tff(c_54,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_66,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_54])).

tff(c_75,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_891,plain,(
    ~ v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_884,c_75])).

tff(c_898,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_891])).

tff(c_899,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1529,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1485,c_899])).

tff(c_1545,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_932,c_64,c_6,c_1222,c_1529])).

tff(c_1548,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_1545])).

tff(c_1552,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_932,c_1026,c_1548])).

tff(c_1553,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1554,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1561,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1553,c_1554])).

tff(c_1568,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1561,c_60])).

tff(c_1575,plain,(
    ! [C_236,A_237,B_238] :
      ( v1_relat_1(C_236)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1579,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1568,c_1575])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1555,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1553,c_8])).

tff(c_1822,plain,(
    ! [C_279,B_280,A_281] :
      ( v5_relat_1(C_279,B_280)
      | ~ m1_subset_1(C_279,k1_zfmisc_1(k2_zfmisc_1(A_281,B_280))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1826,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_1568,c_1822])).

tff(c_1812,plain,(
    ! [B_276,A_277] :
      ( r1_tarski(k2_relat_1(B_276),A_277)
      | ~ v5_relat_1(B_276,A_277)
      | ~ v1_relat_1(B_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1580,plain,(
    ! [B_239,A_240] :
      ( B_239 = A_240
      | ~ r1_tarski(B_239,A_240)
      | ~ r1_tarski(A_240,B_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1585,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1555,c_1580])).

tff(c_1819,plain,(
    ! [B_276] :
      ( k2_relat_1(B_276) = '#skF_1'
      | ~ v5_relat_1(B_276,'#skF_1')
      | ~ v1_relat_1(B_276) ) ),
    inference(resolution,[status(thm)],[c_1812,c_1585])).

tff(c_1829,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1826,c_1819])).

tff(c_1832,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1579,c_1829])).

tff(c_1883,plain,(
    ! [C_289,A_290,B_291] :
      ( v4_relat_1(C_289,A_290)
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(A_290,B_291))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1887,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_1568,c_1883])).

tff(c_1603,plain,(
    ! [B_242,A_243] :
      ( r1_tarski(k1_relat_1(B_242),A_243)
      | ~ v4_relat_1(B_242,A_243)
      | ~ v1_relat_1(B_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1610,plain,(
    ! [B_242] :
      ( k1_relat_1(B_242) = '#skF_1'
      | ~ v4_relat_1(B_242,'#skF_1')
      | ~ v1_relat_1(B_242) ) ),
    inference(resolution,[status(thm)],[c_1603,c_1585])).

tff(c_1890,plain,
    ( k1_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1887,c_1610])).

tff(c_1893,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1579,c_1890])).

tff(c_2038,plain,(
    ! [B_316,A_317] :
      ( m1_subset_1(B_316,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_316),A_317)))
      | ~ r1_tarski(k2_relat_1(B_316),A_317)
      | ~ v1_funct_1(B_316)
      | ~ v1_relat_1(B_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2064,plain,(
    ! [A_317] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_317)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_317)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1893,c_2038])).

tff(c_2073,plain,(
    ! [A_317] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_317))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1579,c_64,c_1555,c_1832,c_2064])).

tff(c_1630,plain,(
    ! [C_251,B_252,A_253] :
      ( v5_relat_1(C_251,B_252)
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(A_253,B_252))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1634,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_1568,c_1630])).

tff(c_1669,plain,(
    ! [B_255,A_256] :
      ( r1_tarski(k2_relat_1(B_255),A_256)
      | ~ v5_relat_1(B_255,A_256)
      | ~ v1_relat_1(B_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1678,plain,(
    ! [B_257] :
      ( k2_relat_1(B_257) = '#skF_1'
      | ~ v5_relat_1(B_257,'#skF_1')
      | ~ v1_relat_1(B_257) ) ),
    inference(resolution,[status(thm)],[c_1669,c_1585])).

tff(c_1681,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1634,c_1678])).

tff(c_1684,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1579,c_1681])).

tff(c_1625,plain,(
    ! [C_248,A_249,B_250] :
      ( v4_relat_1(C_248,A_249)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_249,B_250))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1629,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_1568,c_1625])).

tff(c_1637,plain,
    ( k1_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1629,c_1610])).

tff(c_1640,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1579,c_1637])).

tff(c_1799,plain,(
    ! [B_273,A_274] :
      ( v1_funct_2(B_273,k1_relat_1(B_273),A_274)
      | ~ r1_tarski(k2_relat_1(B_273),A_274)
      | ~ v1_funct_1(B_273)
      | ~ v1_relat_1(B_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1802,plain,(
    ! [A_274] :
      ( v1_funct_2('#skF_4','#skF_1',A_274)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_274)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1640,c_1799])).

tff(c_1804,plain,(
    ! [A_274] : v1_funct_2('#skF_4','#skF_1',A_274) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1579,c_64,c_1555,c_1684,c_1802])).

tff(c_1612,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_1808,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1804,c_1612])).

tff(c_1809,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_2077,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2073,c_1809])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:50:05 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.75/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.65  
% 3.75/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.65  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.75/1.65  
% 3.75/1.65  %Foreground sorts:
% 3.75/1.65  
% 3.75/1.65  
% 3.75/1.65  %Background operators:
% 3.75/1.65  
% 3.75/1.65  
% 3.75/1.65  %Foreground operators:
% 3.75/1.65  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.75/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.75/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.75/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.75/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.75/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.75/1.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.75/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.75/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.75/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.75/1.65  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.75/1.65  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.75/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.75/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.75/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.75/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.75/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.75/1.65  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.75/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.75/1.65  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.75/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.75/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.75/1.65  
% 4.08/1.67  tff(f_133, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_2)).
% 4.08/1.67  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.08/1.67  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.08/1.67  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.08/1.67  tff(f_54, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v5_relat_1(C, A)) => v5_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t218_relat_1)).
% 4.08/1.67  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.08/1.67  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.08/1.67  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.08/1.67  tff(f_113, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 4.08/1.67  tff(f_75, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 4.08/1.67  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.08/1.67  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.08/1.67  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.08/1.67  tff(c_928, plain, (![C_144, A_145, B_146]: (v1_relat_1(C_144) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.08/1.67  tff(c_932, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_928])).
% 4.08/1.67  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.08/1.67  tff(c_58, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.08/1.67  tff(c_980, plain, (![C_162, B_163, A_164]: (v5_relat_1(C_162, B_163) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_164, B_163))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.08/1.67  tff(c_984, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_980])).
% 4.08/1.67  tff(c_985, plain, (![C_165, B_166, A_167]: (v5_relat_1(C_165, B_166) | ~v5_relat_1(C_165, A_167) | ~v1_relat_1(C_165) | ~r1_tarski(A_167, B_166))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.08/1.67  tff(c_987, plain, (![B_166]: (v5_relat_1('#skF_4', B_166) | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', B_166))), inference(resolution, [status(thm)], [c_984, c_985])).
% 4.08/1.67  tff(c_994, plain, (![B_168]: (v5_relat_1('#skF_4', B_168) | ~r1_tarski('#skF_2', B_168))), inference(demodulation, [status(thm), theory('equality')], [c_932, c_987])).
% 4.08/1.67  tff(c_18, plain, (![C_11, B_9, A_8]: (v5_relat_1(C_11, B_9) | ~v5_relat_1(C_11, A_8) | ~v1_relat_1(C_11) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.08/1.67  tff(c_996, plain, (![B_9, B_168]: (v5_relat_1('#skF_4', B_9) | ~v1_relat_1('#skF_4') | ~r1_tarski(B_168, B_9) | ~r1_tarski('#skF_2', B_168))), inference(resolution, [status(thm)], [c_994, c_18])).
% 4.08/1.67  tff(c_1009, plain, (![B_170, B_171]: (v5_relat_1('#skF_4', B_170) | ~r1_tarski(B_171, B_170) | ~r1_tarski('#skF_2', B_171))), inference(demodulation, [status(thm), theory('equality')], [c_932, c_996])).
% 4.08/1.67  tff(c_1019, plain, (v5_relat_1('#skF_4', '#skF_3') | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_1009])).
% 4.08/1.67  tff(c_1026, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1019])).
% 4.08/1.67  tff(c_16, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.08/1.67  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.08/1.68  tff(c_56, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.08/1.68  tff(c_74, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_56])).
% 4.08/1.68  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.08/1.68  tff(c_1063, plain, (![A_175, B_176, C_177]: (k1_relset_1(A_175, B_176, C_177)=k1_relat_1(C_177) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.08/1.68  tff(c_1067, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_1063])).
% 4.08/1.68  tff(c_1211, plain, (![B_215, A_216, C_217]: (k1_xboole_0=B_215 | k1_relset_1(A_216, B_215, C_217)=A_216 | ~v1_funct_2(C_217, A_216, B_215) | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(A_216, B_215))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.08/1.68  tff(c_1217, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_1211])).
% 4.08/1.68  tff(c_1221, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1067, c_1217])).
% 4.08/1.68  tff(c_1222, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_74, c_1221])).
% 4.08/1.68  tff(c_48, plain, (![B_32, A_31]: (m1_subset_1(B_32, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_32), A_31))) | ~r1_tarski(k2_relat_1(B_32), A_31) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.08/1.68  tff(c_1204, plain, (![D_211, B_212, C_213, A_214]: (m1_subset_1(D_211, k1_zfmisc_1(k2_zfmisc_1(B_212, C_213))) | ~r1_tarski(k1_relat_1(D_211), B_212) | ~m1_subset_1(D_211, k1_zfmisc_1(k2_zfmisc_1(A_214, C_213))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.08/1.68  tff(c_1485, plain, (![B_232, B_233, A_234]: (m1_subset_1(B_232, k1_zfmisc_1(k2_zfmisc_1(B_233, A_234))) | ~r1_tarski(k1_relat_1(B_232), B_233) | ~r1_tarski(k2_relat_1(B_232), A_234) | ~v1_funct_1(B_232) | ~v1_relat_1(B_232))), inference(resolution, [status(thm)], [c_48, c_1204])).
% 4.08/1.68  tff(c_103, plain, (![C_38, A_39, B_40]: (v1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.08/1.68  tff(c_107, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_103])).
% 4.08/1.68  tff(c_115, plain, (![C_44, B_45, A_46]: (v5_relat_1(C_44, B_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_46, B_45))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.08/1.68  tff(c_119, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_115])).
% 4.08/1.68  tff(c_160, plain, (![C_59, B_60, A_61]: (v5_relat_1(C_59, B_60) | ~v5_relat_1(C_59, A_61) | ~v1_relat_1(C_59) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.08/1.68  tff(c_164, plain, (![B_60]: (v5_relat_1('#skF_4', B_60) | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', B_60))), inference(resolution, [status(thm)], [c_119, c_160])).
% 4.08/1.68  tff(c_169, plain, (![B_62]: (v5_relat_1('#skF_4', B_62) | ~r1_tarski('#skF_2', B_62))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_164])).
% 4.08/1.68  tff(c_171, plain, (![B_9, B_62]: (v5_relat_1('#skF_4', B_9) | ~v1_relat_1('#skF_4') | ~r1_tarski(B_62, B_9) | ~r1_tarski('#skF_2', B_62))), inference(resolution, [status(thm)], [c_169, c_18])).
% 4.08/1.68  tff(c_183, plain, (![B_63, B_64]: (v5_relat_1('#skF_4', B_63) | ~r1_tarski(B_64, B_63) | ~r1_tarski('#skF_2', B_64))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_171])).
% 4.08/1.68  tff(c_193, plain, (v5_relat_1('#skF_4', '#skF_3') | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_183])).
% 4.08/1.68  tff(c_200, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_193])).
% 4.08/1.68  tff(c_238, plain, (![A_69, B_70, C_71]: (k1_relset_1(A_69, B_70, C_71)=k1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.08/1.68  tff(c_242, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_238])).
% 4.08/1.68  tff(c_631, plain, (![B_130, A_131, C_132]: (k1_xboole_0=B_130 | k1_relset_1(A_131, B_130, C_132)=A_131 | ~v1_funct_2(C_132, A_131, B_130) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_131, B_130))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.08/1.68  tff(c_640, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_631])).
% 4.08/1.68  tff(c_647, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_242, c_640])).
% 4.08/1.68  tff(c_648, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_74, c_647])).
% 4.08/1.68  tff(c_50, plain, (![B_32, A_31]: (v1_funct_2(B_32, k1_relat_1(B_32), A_31) | ~r1_tarski(k2_relat_1(B_32), A_31) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.08/1.68  tff(c_682, plain, (![A_31]: (v1_funct_2('#skF_4', '#skF_1', A_31) | ~r1_tarski(k2_relat_1('#skF_4'), A_31) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_648, c_50])).
% 4.08/1.68  tff(c_871, plain, (![A_139]: (v1_funct_2('#skF_4', '#skF_1', A_139) | ~r1_tarski(k2_relat_1('#skF_4'), A_139))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_64, c_682])).
% 4.08/1.68  tff(c_875, plain, (![A_6]: (v1_funct_2('#skF_4', '#skF_1', A_6) | ~v5_relat_1('#skF_4', A_6) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_871])).
% 4.08/1.68  tff(c_884, plain, (![A_140]: (v1_funct_2('#skF_4', '#skF_1', A_140) | ~v5_relat_1('#skF_4', A_140))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_875])).
% 4.08/1.68  tff(c_54, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.08/1.68  tff(c_66, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_54])).
% 4.08/1.68  tff(c_75, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_66])).
% 4.08/1.68  tff(c_891, plain, (~v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_884, c_75])).
% 4.08/1.68  tff(c_898, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_200, c_891])).
% 4.08/1.68  tff(c_899, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_66])).
% 4.08/1.68  tff(c_1529, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1485, c_899])).
% 4.08/1.68  tff(c_1545, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_932, c_64, c_6, c_1222, c_1529])).
% 4.08/1.68  tff(c_1548, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_1545])).
% 4.08/1.68  tff(c_1552, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_932, c_1026, c_1548])).
% 4.08/1.68  tff(c_1553, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_56])).
% 4.08/1.68  tff(c_1554, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_56])).
% 4.08/1.68  tff(c_1561, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1553, c_1554])).
% 4.08/1.68  tff(c_1568, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1561, c_60])).
% 4.08/1.68  tff(c_1575, plain, (![C_236, A_237, B_238]: (v1_relat_1(C_236) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.08/1.68  tff(c_1579, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1568, c_1575])).
% 4.08/1.68  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.08/1.68  tff(c_1555, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1553, c_8])).
% 4.08/1.68  tff(c_1822, plain, (![C_279, B_280, A_281]: (v5_relat_1(C_279, B_280) | ~m1_subset_1(C_279, k1_zfmisc_1(k2_zfmisc_1(A_281, B_280))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.08/1.68  tff(c_1826, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_1568, c_1822])).
% 4.08/1.68  tff(c_1812, plain, (![B_276, A_277]: (r1_tarski(k2_relat_1(B_276), A_277) | ~v5_relat_1(B_276, A_277) | ~v1_relat_1(B_276))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.08/1.68  tff(c_1580, plain, (![B_239, A_240]: (B_239=A_240 | ~r1_tarski(B_239, A_240) | ~r1_tarski(A_240, B_239))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.08/1.68  tff(c_1585, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(resolution, [status(thm)], [c_1555, c_1580])).
% 4.08/1.68  tff(c_1819, plain, (![B_276]: (k2_relat_1(B_276)='#skF_1' | ~v5_relat_1(B_276, '#skF_1') | ~v1_relat_1(B_276))), inference(resolution, [status(thm)], [c_1812, c_1585])).
% 4.08/1.68  tff(c_1829, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1826, c_1819])).
% 4.08/1.68  tff(c_1832, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1579, c_1829])).
% 4.08/1.68  tff(c_1883, plain, (![C_289, A_290, B_291]: (v4_relat_1(C_289, A_290) | ~m1_subset_1(C_289, k1_zfmisc_1(k2_zfmisc_1(A_290, B_291))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.08/1.68  tff(c_1887, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_1568, c_1883])).
% 4.08/1.68  tff(c_1603, plain, (![B_242, A_243]: (r1_tarski(k1_relat_1(B_242), A_243) | ~v4_relat_1(B_242, A_243) | ~v1_relat_1(B_242))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.08/1.68  tff(c_1610, plain, (![B_242]: (k1_relat_1(B_242)='#skF_1' | ~v4_relat_1(B_242, '#skF_1') | ~v1_relat_1(B_242))), inference(resolution, [status(thm)], [c_1603, c_1585])).
% 4.08/1.68  tff(c_1890, plain, (k1_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1887, c_1610])).
% 4.08/1.68  tff(c_1893, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1579, c_1890])).
% 4.08/1.68  tff(c_2038, plain, (![B_316, A_317]: (m1_subset_1(B_316, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_316), A_317))) | ~r1_tarski(k2_relat_1(B_316), A_317) | ~v1_funct_1(B_316) | ~v1_relat_1(B_316))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.08/1.68  tff(c_2064, plain, (![A_317]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_317))) | ~r1_tarski(k2_relat_1('#skF_4'), A_317) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1893, c_2038])).
% 4.08/1.68  tff(c_2073, plain, (![A_317]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_317))))), inference(demodulation, [status(thm), theory('equality')], [c_1579, c_64, c_1555, c_1832, c_2064])).
% 4.08/1.68  tff(c_1630, plain, (![C_251, B_252, A_253]: (v5_relat_1(C_251, B_252) | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(A_253, B_252))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.08/1.68  tff(c_1634, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_1568, c_1630])).
% 4.08/1.68  tff(c_1669, plain, (![B_255, A_256]: (r1_tarski(k2_relat_1(B_255), A_256) | ~v5_relat_1(B_255, A_256) | ~v1_relat_1(B_255))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.08/1.68  tff(c_1678, plain, (![B_257]: (k2_relat_1(B_257)='#skF_1' | ~v5_relat_1(B_257, '#skF_1') | ~v1_relat_1(B_257))), inference(resolution, [status(thm)], [c_1669, c_1585])).
% 4.08/1.68  tff(c_1681, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1634, c_1678])).
% 4.08/1.68  tff(c_1684, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1579, c_1681])).
% 4.08/1.68  tff(c_1625, plain, (![C_248, A_249, B_250]: (v4_relat_1(C_248, A_249) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_249, B_250))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.08/1.68  tff(c_1629, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_1568, c_1625])).
% 4.08/1.68  tff(c_1637, plain, (k1_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1629, c_1610])).
% 4.08/1.68  tff(c_1640, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1579, c_1637])).
% 4.08/1.68  tff(c_1799, plain, (![B_273, A_274]: (v1_funct_2(B_273, k1_relat_1(B_273), A_274) | ~r1_tarski(k2_relat_1(B_273), A_274) | ~v1_funct_1(B_273) | ~v1_relat_1(B_273))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.08/1.68  tff(c_1802, plain, (![A_274]: (v1_funct_2('#skF_4', '#skF_1', A_274) | ~r1_tarski(k2_relat_1('#skF_4'), A_274) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1640, c_1799])).
% 4.08/1.68  tff(c_1804, plain, (![A_274]: (v1_funct_2('#skF_4', '#skF_1', A_274))), inference(demodulation, [status(thm), theory('equality')], [c_1579, c_64, c_1555, c_1684, c_1802])).
% 4.08/1.68  tff(c_1612, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_66])).
% 4.08/1.68  tff(c_1808, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1804, c_1612])).
% 4.08/1.68  tff(c_1809, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_66])).
% 4.08/1.68  tff(c_2077, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2073, c_1809])).
% 4.08/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.08/1.68  
% 4.08/1.68  Inference rules
% 4.08/1.68  ----------------------
% 4.08/1.68  #Ref     : 0
% 4.08/1.68  #Sup     : 391
% 4.08/1.68  #Fact    : 0
% 4.08/1.68  #Define  : 0
% 4.08/1.68  #Split   : 13
% 4.08/1.68  #Chain   : 0
% 4.08/1.68  #Close   : 0
% 4.08/1.68  
% 4.08/1.68  Ordering : KBO
% 4.08/1.68  
% 4.08/1.68  Simplification rules
% 4.08/1.68  ----------------------
% 4.08/1.68  #Subsume      : 62
% 4.08/1.68  #Demod        : 314
% 4.08/1.68  #Tautology    : 160
% 4.08/1.68  #SimpNegUnit  : 10
% 4.08/1.68  #BackRed      : 19
% 4.08/1.68  
% 4.08/1.68  #Partial instantiations: 0
% 4.08/1.68  #Strategies tried      : 1
% 4.08/1.68  
% 4.08/1.68  Timing (in seconds)
% 4.08/1.68  ----------------------
% 4.18/1.68  Preprocessing        : 0.34
% 4.18/1.68  Parsing              : 0.18
% 4.18/1.68  CNF conversion       : 0.02
% 4.18/1.68  Main loop            : 0.57
% 4.18/1.68  Inferencing          : 0.21
% 4.18/1.68  Reduction            : 0.17
% 4.18/1.68  Demodulation         : 0.12
% 4.18/1.68  BG Simplification    : 0.03
% 4.18/1.68  Subsumption          : 0.11
% 4.18/1.68  Abstraction          : 0.02
% 4.18/1.68  MUC search           : 0.00
% 4.18/1.68  Cooper               : 0.00
% 4.18/1.68  Total                : 0.96
% 4.18/1.68  Index Insertion      : 0.00
% 4.18/1.68  Index Deletion       : 0.00
% 4.18/1.68  Index Matching       : 0.00
% 4.18/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
