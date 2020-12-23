%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:17 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 453 expanded)
%              Number of leaves         :   37 ( 158 expanded)
%              Depth                    :   15
%              Number of atoms          :  218 (1357 expanded)
%              Number of equality atoms :   52 ( 440 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_136,negated_conjecture,(
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

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
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

tff(f_116,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_26,plain,(
    ! [A_20,B_21] : v1_relat_1(k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_102,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_108,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_58,c_102])).

tff(c_113,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_108])).

tff(c_605,plain,(
    ! [C_130,B_131,A_132] :
      ( v5_relat_1(C_130,B_131)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_132,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_620,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_605])).

tff(c_650,plain,(
    ! [B_144,A_145] :
      ( r1_tarski(k2_relat_1(B_144),A_145)
      | ~ v5_relat_1(B_144,A_145)
      | ~ v1_relat_1(B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_56,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_125,plain,(
    ! [A_44,C_45,B_46] :
      ( r1_tarski(A_44,C_45)
      | ~ r1_tarski(B_46,C_45)
      | ~ r1_tarski(A_44,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_128,plain,(
    ! [A_44] :
      ( r1_tarski(A_44,'#skF_4')
      | ~ r1_tarski(A_44,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_56,c_125])).

tff(c_661,plain,(
    ! [B_144] :
      ( r1_tarski(k2_relat_1(B_144),'#skF_4')
      | ~ v5_relat_1(B_144,'#skF_3')
      | ~ v1_relat_1(B_144) ) ),
    inference(resolution,[status(thm)],[c_650,c_128])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_71,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_694,plain,(
    ! [A_152,B_153,C_154] :
      ( k1_relset_1(A_152,B_153,C_154) = k1_relat_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_709,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_694])).

tff(c_969,plain,(
    ! [B_198,A_199,C_200] :
      ( k1_xboole_0 = B_198
      | k1_relset_1(A_199,B_198,C_200) = A_199
      | ~ v1_funct_2(C_200,A_199,B_198)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_199,B_198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_982,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_969])).

tff(c_992,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_709,c_982])).

tff(c_993,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_992])).

tff(c_46,plain,(
    ! [B_32,A_31] :
      ( m1_subset_1(B_32,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_32),A_31)))
      | ~ r1_tarski(k2_relat_1(B_32),A_31)
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1000,plain,(
    ! [A_31] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_31)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_31)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_993,c_46])).

tff(c_1030,plain,(
    ! [A_202] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_202)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_62,c_1000])).

tff(c_52,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_64,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52])).

tff(c_130,plain,(
    ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_177,plain,(
    ! [C_59,B_60,A_61] :
      ( v5_relat_1(C_59,B_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_61,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_192,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_177])).

tff(c_200,plain,(
    ! [B_65,A_66] :
      ( r1_tarski(k2_relat_1(B_65),A_66)
      | ~ v5_relat_1(B_65,A_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_207,plain,(
    ! [B_65] :
      ( r1_tarski(k2_relat_1(B_65),'#skF_4')
      | ~ v5_relat_1(B_65,'#skF_3')
      | ~ v1_relat_1(B_65) ) ),
    inference(resolution,[status(thm)],[c_200,c_128])).

tff(c_244,plain,(
    ! [A_75,B_76,C_77] :
      ( k1_relset_1(A_75,B_76,C_77) = k1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_259,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_244])).

tff(c_519,plain,(
    ! [B_121,A_122,C_123] :
      ( k1_xboole_0 = B_121
      | k1_relset_1(A_122,B_121,C_123) = A_122
      | ~ v1_funct_2(C_123,A_122,B_121)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_122,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_532,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_519])).

tff(c_542,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_259,c_532])).

tff(c_543,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_542])).

tff(c_48,plain,(
    ! [B_32,A_31] :
      ( v1_funct_2(B_32,k1_relat_1(B_32),A_31)
      | ~ r1_tarski(k2_relat_1(B_32),A_31)
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_553,plain,(
    ! [A_31] :
      ( v1_funct_2('#skF_5','#skF_2',A_31)
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_31)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_543,c_48])).

tff(c_565,plain,(
    ! [A_124] :
      ( v1_funct_2('#skF_5','#skF_2',A_124)
      | ~ r1_tarski(k2_relat_1('#skF_5'),A_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_62,c_553])).

tff(c_569,plain,
    ( v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_207,c_565])).

tff(c_576,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_192,c_569])).

tff(c_578,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_576])).

tff(c_579,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1069,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1030,c_579])).

tff(c_1075,plain,
    ( ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_661,c_1069])).

tff(c_1082,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_620,c_1075])).

tff(c_1084,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1135,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1084,c_4])).

tff(c_1083,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1090,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1084,c_1083])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1085,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1083,c_2])).

tff(c_1095,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1090,c_1085])).

tff(c_10,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1103,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1084,c_1084,c_10])).

tff(c_1113,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1103,c_1090,c_58])).

tff(c_1180,plain,(
    ! [C_220,B_221,A_222] :
      ( ~ v1_xboole_0(C_220)
      | ~ m1_subset_1(B_221,k1_zfmisc_1(C_220))
      | ~ r2_hidden(A_222,B_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1182,plain,(
    ! [A_222] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_222,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1113,c_1180])).

tff(c_1189,plain,(
    ! [A_223] : ~ r2_hidden(A_223,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1095,c_1182])).

tff(c_1194,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1135,c_1189])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1101,plain,(
    ! [A_8] : m1_subset_1('#skF_3',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1084,c_14])).

tff(c_12,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1114,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_3',B_7) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1084,c_1084,c_12])).

tff(c_1227,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1194,c_1090,c_1101,c_1194,c_1114,c_1090,c_64])).

tff(c_1104,plain,(
    ! [A_204] : k2_zfmisc_1(A_204,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1084,c_1084,c_10])).

tff(c_1108,plain,(
    v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1104,c_26])).

tff(c_1206,plain,(
    ! [C_224,B_225,A_226] :
      ( v5_relat_1(C_224,B_225)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_226,B_225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1217,plain,(
    ! [B_225] : v5_relat_1('#skF_3',B_225) ),
    inference(resolution,[status(thm)],[c_1101,c_1206])).

tff(c_1167,plain,(
    ! [B_218,A_219] :
      ( r1_tarski(k2_relat_1(B_218),A_219)
      | ~ v5_relat_1(B_218,A_219)
      | ~ v1_relat_1(B_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1162,plain,(
    ! [A_214,C_215,B_216] :
      ( r1_tarski(A_214,C_215)
      | ~ r1_tarski(B_216,C_215)
      | ~ r1_tarski(A_214,B_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1165,plain,(
    ! [A_214] :
      ( r1_tarski(A_214,'#skF_4')
      | ~ r1_tarski(A_214,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_56,c_1162])).

tff(c_1177,plain,(
    ! [B_218] :
      ( r1_tarski(k2_relat_1(B_218),'#skF_4')
      | ~ v5_relat_1(B_218,'#skF_3')
      | ~ v1_relat_1(B_218) ) ),
    inference(resolution,[status(thm)],[c_1167,c_1165])).

tff(c_1199,plain,(
    v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1194,c_62])).

tff(c_1294,plain,(
    ! [A_245,B_246,C_247] :
      ( k1_relset_1(A_245,B_246,C_247) = k1_relat_1(C_247)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_245,B_246))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1305,plain,(
    ! [A_245,B_246] : k1_relset_1(A_245,B_246,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1101,c_1294])).

tff(c_1096,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1090,c_60])).

tff(c_1198,plain,(
    v1_funct_2('#skF_3','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1194,c_1096])).

tff(c_42,plain,(
    ! [B_29,C_30] :
      ( k1_relset_1(k1_xboole_0,B_29,C_30) = k1_xboole_0
      | ~ v1_funct_2(C_30,k1_xboole_0,B_29)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_67,plain,(
    ! [B_29,C_30] :
      ( k1_relset_1(k1_xboole_0,B_29,C_30) = k1_xboole_0
      | ~ v1_funct_2(C_30,k1_xboole_0,B_29)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_42])).

tff(c_1342,plain,(
    ! [B_261,C_262] :
      ( k1_relset_1('#skF_3',B_261,C_262) = '#skF_3'
      | ~ v1_funct_2(C_262,'#skF_3',B_261)
      | ~ m1_subset_1(C_262,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1084,c_1084,c_1084,c_1084,c_67])).

tff(c_1344,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1198,c_1342])).

tff(c_1350,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1101,c_1305,c_1344])).

tff(c_1359,plain,(
    ! [A_31] :
      ( v1_funct_2('#skF_3','#skF_3',A_31)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_31)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1350,c_48])).

tff(c_1372,plain,(
    ! [A_265] :
      ( v1_funct_2('#skF_3','#skF_3',A_265)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_265) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1108,c_1199,c_1359])).

tff(c_1376,plain,
    ( v1_funct_2('#skF_3','#skF_3','#skF_4')
    | ~ v5_relat_1('#skF_3','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1177,c_1372])).

tff(c_1383,plain,(
    v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1108,c_1217,c_1376])).

tff(c_1385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1227,c_1383])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:31:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.52  
% 3.31/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.52  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.31/1.52  
% 3.31/1.52  %Foreground sorts:
% 3.31/1.52  
% 3.31/1.52  
% 3.31/1.52  %Background operators:
% 3.31/1.52  
% 3.31/1.52  
% 3.31/1.52  %Foreground operators:
% 3.31/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.31/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.31/1.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.31/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.31/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.31/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.31/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.31/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.31/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.31/1.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.31/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.31/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.31/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.31/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.31/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.31/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.31/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.31/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.31/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.31/1.52  
% 3.52/1.55  tff(f_76, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.52/1.55  tff(f_136, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 3.52/1.55  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.52/1.55  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.52/1.55  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.52/1.55  tff(f_40, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.52/1.55  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.52/1.55  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.52/1.55  tff(f_116, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 3.52/1.55  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.52/1.55  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.52/1.55  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.52/1.55  tff(f_61, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.52/1.55  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.52/1.55  tff(c_26, plain, (![A_20, B_21]: (v1_relat_1(k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.52/1.55  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.52/1.55  tff(c_102, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.52/1.55  tff(c_108, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_58, c_102])).
% 3.52/1.55  tff(c_113, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_108])).
% 3.52/1.55  tff(c_605, plain, (![C_130, B_131, A_132]: (v5_relat_1(C_130, B_131) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_132, B_131))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.52/1.55  tff(c_620, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_605])).
% 3.52/1.55  tff(c_650, plain, (![B_144, A_145]: (r1_tarski(k2_relat_1(B_144), A_145) | ~v5_relat_1(B_144, A_145) | ~v1_relat_1(B_144))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.52/1.55  tff(c_56, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.52/1.55  tff(c_125, plain, (![A_44, C_45, B_46]: (r1_tarski(A_44, C_45) | ~r1_tarski(B_46, C_45) | ~r1_tarski(A_44, B_46))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.52/1.55  tff(c_128, plain, (![A_44]: (r1_tarski(A_44, '#skF_4') | ~r1_tarski(A_44, '#skF_3'))), inference(resolution, [status(thm)], [c_56, c_125])).
% 3.52/1.55  tff(c_661, plain, (![B_144]: (r1_tarski(k2_relat_1(B_144), '#skF_4') | ~v5_relat_1(B_144, '#skF_3') | ~v1_relat_1(B_144))), inference(resolution, [status(thm)], [c_650, c_128])).
% 3.52/1.55  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.52/1.55  tff(c_54, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.52/1.55  tff(c_71, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_54])).
% 3.52/1.55  tff(c_60, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.52/1.55  tff(c_694, plain, (![A_152, B_153, C_154]: (k1_relset_1(A_152, B_153, C_154)=k1_relat_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.52/1.55  tff(c_709, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_694])).
% 3.52/1.55  tff(c_969, plain, (![B_198, A_199, C_200]: (k1_xboole_0=B_198 | k1_relset_1(A_199, B_198, C_200)=A_199 | ~v1_funct_2(C_200, A_199, B_198) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_199, B_198))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.52/1.55  tff(c_982, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_969])).
% 3.52/1.55  tff(c_992, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_709, c_982])).
% 3.52/1.55  tff(c_993, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_71, c_992])).
% 3.52/1.55  tff(c_46, plain, (![B_32, A_31]: (m1_subset_1(B_32, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_32), A_31))) | ~r1_tarski(k2_relat_1(B_32), A_31) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.52/1.55  tff(c_1000, plain, (![A_31]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_31))) | ~r1_tarski(k2_relat_1('#skF_5'), A_31) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_993, c_46])).
% 3.52/1.55  tff(c_1030, plain, (![A_202]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_202))) | ~r1_tarski(k2_relat_1('#skF_5'), A_202))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_62, c_1000])).
% 3.52/1.55  tff(c_52, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.52/1.55  tff(c_64, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52])).
% 3.52/1.55  tff(c_130, plain, (~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_64])).
% 3.52/1.55  tff(c_177, plain, (![C_59, B_60, A_61]: (v5_relat_1(C_59, B_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_61, B_60))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.52/1.55  tff(c_192, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_177])).
% 3.52/1.55  tff(c_200, plain, (![B_65, A_66]: (r1_tarski(k2_relat_1(B_65), A_66) | ~v5_relat_1(B_65, A_66) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.52/1.55  tff(c_207, plain, (![B_65]: (r1_tarski(k2_relat_1(B_65), '#skF_4') | ~v5_relat_1(B_65, '#skF_3') | ~v1_relat_1(B_65))), inference(resolution, [status(thm)], [c_200, c_128])).
% 3.52/1.55  tff(c_244, plain, (![A_75, B_76, C_77]: (k1_relset_1(A_75, B_76, C_77)=k1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.52/1.55  tff(c_259, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_244])).
% 3.52/1.55  tff(c_519, plain, (![B_121, A_122, C_123]: (k1_xboole_0=B_121 | k1_relset_1(A_122, B_121, C_123)=A_122 | ~v1_funct_2(C_123, A_122, B_121) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_122, B_121))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.52/1.55  tff(c_532, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_519])).
% 3.52/1.55  tff(c_542, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_259, c_532])).
% 3.52/1.55  tff(c_543, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_71, c_542])).
% 3.52/1.55  tff(c_48, plain, (![B_32, A_31]: (v1_funct_2(B_32, k1_relat_1(B_32), A_31) | ~r1_tarski(k2_relat_1(B_32), A_31) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.52/1.55  tff(c_553, plain, (![A_31]: (v1_funct_2('#skF_5', '#skF_2', A_31) | ~r1_tarski(k2_relat_1('#skF_5'), A_31) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_543, c_48])).
% 3.52/1.55  tff(c_565, plain, (![A_124]: (v1_funct_2('#skF_5', '#skF_2', A_124) | ~r1_tarski(k2_relat_1('#skF_5'), A_124))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_62, c_553])).
% 3.52/1.55  tff(c_569, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_4') | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_207, c_565])).
% 3.52/1.55  tff(c_576, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_192, c_569])).
% 3.52/1.55  tff(c_578, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_576])).
% 3.52/1.55  tff(c_579, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(splitRight, [status(thm)], [c_64])).
% 3.52/1.55  tff(c_1069, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_1030, c_579])).
% 3.52/1.55  tff(c_1075, plain, (~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_661, c_1069])).
% 3.52/1.55  tff(c_1082, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_620, c_1075])).
% 3.52/1.55  tff(c_1084, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_54])).
% 3.52/1.55  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.52/1.55  tff(c_1135, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1084, c_4])).
% 3.52/1.55  tff(c_1083, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_54])).
% 3.52/1.55  tff(c_1090, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1084, c_1083])).
% 3.52/1.55  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.52/1.55  tff(c_1085, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1083, c_2])).
% 3.52/1.55  tff(c_1095, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1090, c_1085])).
% 3.52/1.55  tff(c_10, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.52/1.55  tff(c_1103, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1084, c_1084, c_10])).
% 3.52/1.55  tff(c_1113, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1103, c_1090, c_58])).
% 3.52/1.55  tff(c_1180, plain, (![C_220, B_221, A_222]: (~v1_xboole_0(C_220) | ~m1_subset_1(B_221, k1_zfmisc_1(C_220)) | ~r2_hidden(A_222, B_221))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.52/1.55  tff(c_1182, plain, (![A_222]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_222, '#skF_5'))), inference(resolution, [status(thm)], [c_1113, c_1180])).
% 3.52/1.55  tff(c_1189, plain, (![A_223]: (~r2_hidden(A_223, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1095, c_1182])).
% 3.52/1.55  tff(c_1194, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_1135, c_1189])).
% 3.52/1.55  tff(c_14, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.52/1.55  tff(c_1101, plain, (![A_8]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_1084, c_14])).
% 3.52/1.55  tff(c_12, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.52/1.55  tff(c_1114, plain, (![B_7]: (k2_zfmisc_1('#skF_3', B_7)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1084, c_1084, c_12])).
% 3.52/1.55  tff(c_1227, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1194, c_1090, c_1101, c_1194, c_1114, c_1090, c_64])).
% 3.52/1.55  tff(c_1104, plain, (![A_204]: (k2_zfmisc_1(A_204, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1084, c_1084, c_10])).
% 3.52/1.55  tff(c_1108, plain, (v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1104, c_26])).
% 3.52/1.55  tff(c_1206, plain, (![C_224, B_225, A_226]: (v5_relat_1(C_224, B_225) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_226, B_225))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.52/1.55  tff(c_1217, plain, (![B_225]: (v5_relat_1('#skF_3', B_225))), inference(resolution, [status(thm)], [c_1101, c_1206])).
% 3.52/1.55  tff(c_1167, plain, (![B_218, A_219]: (r1_tarski(k2_relat_1(B_218), A_219) | ~v5_relat_1(B_218, A_219) | ~v1_relat_1(B_218))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.52/1.55  tff(c_1162, plain, (![A_214, C_215, B_216]: (r1_tarski(A_214, C_215) | ~r1_tarski(B_216, C_215) | ~r1_tarski(A_214, B_216))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.52/1.55  tff(c_1165, plain, (![A_214]: (r1_tarski(A_214, '#skF_4') | ~r1_tarski(A_214, '#skF_3'))), inference(resolution, [status(thm)], [c_56, c_1162])).
% 3.52/1.55  tff(c_1177, plain, (![B_218]: (r1_tarski(k2_relat_1(B_218), '#skF_4') | ~v5_relat_1(B_218, '#skF_3') | ~v1_relat_1(B_218))), inference(resolution, [status(thm)], [c_1167, c_1165])).
% 3.52/1.55  tff(c_1199, plain, (v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1194, c_62])).
% 3.52/1.55  tff(c_1294, plain, (![A_245, B_246, C_247]: (k1_relset_1(A_245, B_246, C_247)=k1_relat_1(C_247) | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_245, B_246))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.52/1.55  tff(c_1305, plain, (![A_245, B_246]: (k1_relset_1(A_245, B_246, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1101, c_1294])).
% 3.52/1.55  tff(c_1096, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1090, c_60])).
% 3.52/1.55  tff(c_1198, plain, (v1_funct_2('#skF_3', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1194, c_1096])).
% 3.52/1.55  tff(c_42, plain, (![B_29, C_30]: (k1_relset_1(k1_xboole_0, B_29, C_30)=k1_xboole_0 | ~v1_funct_2(C_30, k1_xboole_0, B_29) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_29))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.52/1.55  tff(c_67, plain, (![B_29, C_30]: (k1_relset_1(k1_xboole_0, B_29, C_30)=k1_xboole_0 | ~v1_funct_2(C_30, k1_xboole_0, B_29) | ~m1_subset_1(C_30, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_42])).
% 3.52/1.55  tff(c_1342, plain, (![B_261, C_262]: (k1_relset_1('#skF_3', B_261, C_262)='#skF_3' | ~v1_funct_2(C_262, '#skF_3', B_261) | ~m1_subset_1(C_262, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1084, c_1084, c_1084, c_1084, c_67])).
% 3.52/1.55  tff(c_1344, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_1198, c_1342])).
% 3.52/1.55  tff(c_1350, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1101, c_1305, c_1344])).
% 3.52/1.55  tff(c_1359, plain, (![A_31]: (v1_funct_2('#skF_3', '#skF_3', A_31) | ~r1_tarski(k2_relat_1('#skF_3'), A_31) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1350, c_48])).
% 3.52/1.55  tff(c_1372, plain, (![A_265]: (v1_funct_2('#skF_3', '#skF_3', A_265) | ~r1_tarski(k2_relat_1('#skF_3'), A_265))), inference(demodulation, [status(thm), theory('equality')], [c_1108, c_1199, c_1359])).
% 3.52/1.55  tff(c_1376, plain, (v1_funct_2('#skF_3', '#skF_3', '#skF_4') | ~v5_relat_1('#skF_3', '#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1177, c_1372])).
% 3.52/1.55  tff(c_1383, plain, (v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1108, c_1217, c_1376])).
% 3.52/1.55  tff(c_1385, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1227, c_1383])).
% 3.52/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.55  
% 3.52/1.55  Inference rules
% 3.52/1.55  ----------------------
% 3.52/1.55  #Ref     : 0
% 3.52/1.55  #Sup     : 269
% 3.52/1.55  #Fact    : 0
% 3.52/1.55  #Define  : 0
% 3.52/1.55  #Split   : 10
% 3.52/1.55  #Chain   : 0
% 3.61/1.55  #Close   : 0
% 3.61/1.55  
% 3.61/1.55  Ordering : KBO
% 3.61/1.55  
% 3.61/1.55  Simplification rules
% 3.61/1.55  ----------------------
% 3.61/1.55  #Subsume      : 31
% 3.61/1.55  #Demod        : 179
% 3.61/1.55  #Tautology    : 115
% 3.61/1.55  #SimpNegUnit  : 8
% 3.61/1.55  #BackRed      : 14
% 3.61/1.55  
% 3.61/1.55  #Partial instantiations: 0
% 3.61/1.55  #Strategies tried      : 1
% 3.61/1.55  
% 3.61/1.55  Timing (in seconds)
% 3.61/1.55  ----------------------
% 3.61/1.55  Preprocessing        : 0.30
% 3.61/1.55  Parsing              : 0.15
% 3.61/1.55  CNF conversion       : 0.02
% 3.61/1.55  Main loop            : 0.44
% 3.61/1.55  Inferencing          : 0.17
% 3.61/1.55  Reduction            : 0.14
% 3.61/1.55  Demodulation         : 0.10
% 3.61/1.55  BG Simplification    : 0.02
% 3.61/1.55  Subsumption          : 0.08
% 3.61/1.55  Abstraction          : 0.02
% 3.61/1.55  MUC search           : 0.00
% 3.61/1.55  Cooper               : 0.00
% 3.61/1.55  Total                : 0.78
% 3.61/1.55  Index Insertion      : 0.00
% 3.61/1.55  Index Deletion       : 0.00
% 3.61/1.55  Index Matching       : 0.00
% 3.61/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
