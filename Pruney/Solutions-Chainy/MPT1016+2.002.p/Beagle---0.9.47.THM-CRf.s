%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:40 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 301 expanded)
%              Number of leaves         :   36 ( 116 expanded)
%              Depth                    :   15
%              Number of atoms          :  232 (1019 expanded)
%              Number of equality atoms :   51 ( 246 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_113,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
        <=> ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_88,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_97,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_88])).

tff(c_172,plain,(
    ! [C_73,A_74,B_75] :
      ( v4_relat_1(C_73,A_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_181,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_172])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_relat_1(B_13),A_12)
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_46,plain,
    ( '#skF_5' != '#skF_6'
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_67,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_217,plain,(
    ! [A_91] :
      ( r2_hidden('#skF_1'(A_91),k1_relat_1(A_91))
      | v2_funct_1(A_91)
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10,plain,(
    ! [C_6,A_3,B_4] :
      ( r2_hidden(C_6,A_3)
      | ~ r2_hidden(C_6,B_4)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_400,plain,(
    ! [A_145,A_146] :
      ( r2_hidden('#skF_1'(A_145),A_146)
      | ~ m1_subset_1(k1_relat_1(A_145),k1_zfmisc_1(A_146))
      | v2_funct_1(A_145)
      | ~ v1_funct_1(A_145)
      | ~ v1_relat_1(A_145) ) ),
    inference(resolution,[status(thm)],[c_217,c_10])).

tff(c_405,plain,(
    ! [A_145,B_8] :
      ( r2_hidden('#skF_1'(A_145),B_8)
      | v2_funct_1(A_145)
      | ~ v1_funct_1(A_145)
      | ~ v1_relat_1(A_145)
      | ~ r1_tarski(k1_relat_1(A_145),B_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_400])).

tff(c_199,plain,(
    ! [A_81] :
      ( '#skF_2'(A_81) != '#skF_1'(A_81)
      | v2_funct_1(A_81)
      | ~ v1_funct_1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_202,plain,
    ( '#skF_2'('#skF_4') != '#skF_1'('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_199,c_67])).

tff(c_205,plain,(
    '#skF_2'('#skF_4') != '#skF_1'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_44,c_202])).

tff(c_224,plain,(
    ! [A_92] :
      ( r2_hidden('#skF_2'(A_92),k1_relat_1(A_92))
      | v2_funct_1(A_92)
      | ~ v1_funct_1(A_92)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_413,plain,(
    ! [A_149,A_150] :
      ( r2_hidden('#skF_2'(A_149),A_150)
      | ~ m1_subset_1(k1_relat_1(A_149),k1_zfmisc_1(A_150))
      | v2_funct_1(A_149)
      | ~ v1_funct_1(A_149)
      | ~ v1_relat_1(A_149) ) ),
    inference(resolution,[status(thm)],[c_224,c_10])).

tff(c_420,plain,(
    ! [A_151,B_152] :
      ( r2_hidden('#skF_2'(A_151),B_152)
      | v2_funct_1(A_151)
      | ~ v1_funct_1(A_151)
      | ~ v1_relat_1(A_151)
      | ~ r1_tarski(k1_relat_1(A_151),B_152) ) ),
    inference(resolution,[status(thm)],[c_14,c_413])).

tff(c_231,plain,(
    ! [A_93] :
      ( k1_funct_1(A_93,'#skF_2'(A_93)) = k1_funct_1(A_93,'#skF_1'(A_93))
      | v2_funct_1(A_93)
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_64,plain,(
    ! [D_36,C_35] :
      ( v2_funct_1('#skF_4')
      | D_36 = C_35
      | k1_funct_1('#skF_4',D_36) != k1_funct_1('#skF_4',C_35)
      | ~ r2_hidden(D_36,'#skF_3')
      | ~ r2_hidden(C_35,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_117,plain,(
    ! [D_36,C_35] :
      ( D_36 = C_35
      | k1_funct_1('#skF_4',D_36) != k1_funct_1('#skF_4',C_35)
      | ~ r2_hidden(D_36,'#skF_3')
      | ~ r2_hidden(C_35,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_64])).

tff(c_237,plain,(
    ! [C_35] :
      ( C_35 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_35) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_35,'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_117])).

tff(c_246,plain,(
    ! [C_35] :
      ( C_35 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_35) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_35,'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_44,c_237])).

tff(c_247,plain,(
    ! [C_35] :
      ( C_35 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_35) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_35,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_246])).

tff(c_419,plain,(
    ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_247])).

tff(c_423,plain,
    ( v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_420,c_419])).

tff(c_430,plain,
    ( v2_funct_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_44,c_423])).

tff(c_431,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_430])).

tff(c_436,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_431])).

tff(c_440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_181,c_436])).

tff(c_442,plain,(
    r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_240,plain,(
    ! [D_36] :
      ( D_36 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_36) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_36,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_117])).

tff(c_249,plain,(
    ! [D_36] :
      ( D_36 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_36) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_36,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_44,c_240])).

tff(c_250,plain,(
    ! [D_36] :
      ( D_36 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_36) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_36,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_249])).

tff(c_495,plain,(
    ! [D_36] :
      ( D_36 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_36) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_36,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_250])).

tff(c_498,plain,
    ( '#skF_2'('#skF_4') = '#skF_1'('#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_495])).

tff(c_499,plain,(
    ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_205,c_498])).

tff(c_511,plain,
    ( v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_405,c_499])).

tff(c_514,plain,
    ( v2_funct_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_44,c_511])).

tff(c_515,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_514])).

tff(c_518,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_515])).

tff(c_522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_181,c_518])).

tff(c_524,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_50,plain,
    ( r2_hidden('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_528,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_50])).

tff(c_607,plain,(
    ! [C_188,B_189,A_190] :
      ( ~ v1_xboole_0(C_188)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(C_188))
      | ~ r2_hidden(A_190,B_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_633,plain,(
    ! [B_193,A_194,A_195] :
      ( ~ v1_xboole_0(B_193)
      | ~ r2_hidden(A_194,A_195)
      | ~ r1_tarski(A_195,B_193) ) ),
    inference(resolution,[status(thm)],[c_14,c_607])).

tff(c_640,plain,(
    ! [B_196] :
      ( ~ v1_xboole_0(B_196)
      | ~ r1_tarski('#skF_3',B_196) ) ),
    inference(resolution,[status(thm)],[c_528,c_633])).

tff(c_645,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_640])).

tff(c_42,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_48,plain,
    ( k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_535,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_48])).

tff(c_52,plain,
    ( r2_hidden('#skF_5','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_526,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_52])).

tff(c_910,plain,(
    ! [D_270,C_271,B_272,A_273] :
      ( k1_funct_1(k2_funct_1(D_270),k1_funct_1(D_270,C_271)) = C_271
      | k1_xboole_0 = B_272
      | ~ r2_hidden(C_271,A_273)
      | ~ v2_funct_1(D_270)
      | ~ m1_subset_1(D_270,k1_zfmisc_1(k2_zfmisc_1(A_273,B_272)))
      | ~ v1_funct_2(D_270,A_273,B_272)
      | ~ v1_funct_1(D_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_956,plain,(
    ! [D_284,B_285] :
      ( k1_funct_1(k2_funct_1(D_284),k1_funct_1(D_284,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = B_285
      | ~ v2_funct_1(D_284)
      | ~ m1_subset_1(D_284,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_285)))
      | ~ v1_funct_2(D_284,'#skF_3',B_285)
      | ~ v1_funct_1(D_284) ) ),
    inference(resolution,[status(thm)],[c_526,c_910])).

tff(c_961,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_956])).

tff(c_965,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_524,c_535,c_961])).

tff(c_966,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_965])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_969,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_966,c_2])).

tff(c_971,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_645,c_969])).

tff(c_973,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_965])).

tff(c_523,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_972,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_965])).

tff(c_1015,plain,(
    ! [D_299,B_300] :
      ( k1_funct_1(k2_funct_1(D_299),k1_funct_1(D_299,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_300
      | ~ v2_funct_1(D_299)
      | ~ m1_subset_1(D_299,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_300)))
      | ~ v1_funct_2(D_299,'#skF_3',B_300)
      | ~ v1_funct_1(D_299) ) ),
    inference(resolution,[status(thm)],[c_528,c_910])).

tff(c_1020,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_1015])).

tff(c_1024,plain,
    ( '#skF_5' = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_524,c_972,c_1020])).

tff(c_1026,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_973,c_523,c_1024])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:28:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.50  
% 3.28/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.50  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 3.28/1.50  
% 3.28/1.50  %Foreground sorts:
% 3.28/1.50  
% 3.28/1.50  
% 3.28/1.50  %Background operators:
% 3.28/1.50  
% 3.28/1.50  
% 3.28/1.50  %Foreground operators:
% 3.28/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.28/1.50  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.28/1.50  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.28/1.50  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.28/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.28/1.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.28/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.28/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.28/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.28/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.28/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.28/1.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.28/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.28/1.50  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.28/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.28/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.28/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.28/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.28/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.28/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.28/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.28/1.50  
% 3.28/1.52  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.28/1.52  tff(f_113, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_funct_2)).
% 3.28/1.52  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.28/1.52  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.28/1.52  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.28/1.52  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.28/1.52  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 3.28/1.52  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.28/1.52  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.28/1.52  tff(f_95, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 3.28/1.52  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.28/1.52  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.28/1.52  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.28/1.52  tff(c_88, plain, (![C_44, A_45, B_46]: (v1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.28/1.52  tff(c_97, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_88])).
% 3.28/1.52  tff(c_172, plain, (![C_73, A_74, B_75]: (v4_relat_1(C_73, A_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.28/1.52  tff(c_181, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_172])).
% 3.28/1.52  tff(c_20, plain, (![B_13, A_12]: (r1_tarski(k1_relat_1(B_13), A_12) | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.28/1.52  tff(c_46, plain, ('#skF_5'!='#skF_6' | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.28/1.52  tff(c_67, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_46])).
% 3.28/1.52  tff(c_44, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.28/1.52  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.28/1.52  tff(c_217, plain, (![A_91]: (r2_hidden('#skF_1'(A_91), k1_relat_1(A_91)) | v2_funct_1(A_91) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.28/1.52  tff(c_10, plain, (![C_6, A_3, B_4]: (r2_hidden(C_6, A_3) | ~r2_hidden(C_6, B_4) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.28/1.52  tff(c_400, plain, (![A_145, A_146]: (r2_hidden('#skF_1'(A_145), A_146) | ~m1_subset_1(k1_relat_1(A_145), k1_zfmisc_1(A_146)) | v2_funct_1(A_145) | ~v1_funct_1(A_145) | ~v1_relat_1(A_145))), inference(resolution, [status(thm)], [c_217, c_10])).
% 3.28/1.52  tff(c_405, plain, (![A_145, B_8]: (r2_hidden('#skF_1'(A_145), B_8) | v2_funct_1(A_145) | ~v1_funct_1(A_145) | ~v1_relat_1(A_145) | ~r1_tarski(k1_relat_1(A_145), B_8))), inference(resolution, [status(thm)], [c_14, c_400])).
% 3.28/1.52  tff(c_199, plain, (![A_81]: ('#skF_2'(A_81)!='#skF_1'(A_81) | v2_funct_1(A_81) | ~v1_funct_1(A_81) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.28/1.52  tff(c_202, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_199, c_67])).
% 3.28/1.52  tff(c_205, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_44, c_202])).
% 3.28/1.52  tff(c_224, plain, (![A_92]: (r2_hidden('#skF_2'(A_92), k1_relat_1(A_92)) | v2_funct_1(A_92) | ~v1_funct_1(A_92) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.28/1.52  tff(c_413, plain, (![A_149, A_150]: (r2_hidden('#skF_2'(A_149), A_150) | ~m1_subset_1(k1_relat_1(A_149), k1_zfmisc_1(A_150)) | v2_funct_1(A_149) | ~v1_funct_1(A_149) | ~v1_relat_1(A_149))), inference(resolution, [status(thm)], [c_224, c_10])).
% 3.28/1.52  tff(c_420, plain, (![A_151, B_152]: (r2_hidden('#skF_2'(A_151), B_152) | v2_funct_1(A_151) | ~v1_funct_1(A_151) | ~v1_relat_1(A_151) | ~r1_tarski(k1_relat_1(A_151), B_152))), inference(resolution, [status(thm)], [c_14, c_413])).
% 3.28/1.52  tff(c_231, plain, (![A_93]: (k1_funct_1(A_93, '#skF_2'(A_93))=k1_funct_1(A_93, '#skF_1'(A_93)) | v2_funct_1(A_93) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.28/1.52  tff(c_64, plain, (![D_36, C_35]: (v2_funct_1('#skF_4') | D_36=C_35 | k1_funct_1('#skF_4', D_36)!=k1_funct_1('#skF_4', C_35) | ~r2_hidden(D_36, '#skF_3') | ~r2_hidden(C_35, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.28/1.52  tff(c_117, plain, (![D_36, C_35]: (D_36=C_35 | k1_funct_1('#skF_4', D_36)!=k1_funct_1('#skF_4', C_35) | ~r2_hidden(D_36, '#skF_3') | ~r2_hidden(C_35, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_67, c_64])).
% 3.28/1.52  tff(c_237, plain, (![C_35]: (C_35='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_35)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_35, '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_231, c_117])).
% 3.28/1.52  tff(c_246, plain, (![C_35]: (C_35='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_35)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_35, '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_44, c_237])).
% 3.28/1.52  tff(c_247, plain, (![C_35]: (C_35='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_35)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_35, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_67, c_246])).
% 3.28/1.52  tff(c_419, plain, (~r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_247])).
% 3.28/1.52  tff(c_423, plain, (v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_420, c_419])).
% 3.28/1.52  tff(c_430, plain, (v2_funct_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_44, c_423])).
% 3.28/1.52  tff(c_431, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_67, c_430])).
% 3.28/1.52  tff(c_436, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_431])).
% 3.28/1.52  tff(c_440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97, c_181, c_436])).
% 3.28/1.52  tff(c_442, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_247])).
% 3.28/1.52  tff(c_240, plain, (![D_36]: (D_36='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_36)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_36, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_231, c_117])).
% 3.28/1.52  tff(c_249, plain, (![D_36]: (D_36='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_36)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_36, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_44, c_240])).
% 3.28/1.52  tff(c_250, plain, (![D_36]: (D_36='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_36)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_36, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_67, c_249])).
% 3.28/1.52  tff(c_495, plain, (![D_36]: (D_36='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_36)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_36, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_442, c_250])).
% 3.28/1.52  tff(c_498, plain, ('#skF_2'('#skF_4')='#skF_1'('#skF_4') | ~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_495])).
% 3.28/1.52  tff(c_499, plain, (~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_205, c_498])).
% 3.28/1.52  tff(c_511, plain, (v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_405, c_499])).
% 3.28/1.52  tff(c_514, plain, (v2_funct_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_44, c_511])).
% 3.28/1.52  tff(c_515, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_67, c_514])).
% 3.28/1.52  tff(c_518, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_515])).
% 3.28/1.52  tff(c_522, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97, c_181, c_518])).
% 3.28/1.52  tff(c_524, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_46])).
% 3.28/1.52  tff(c_50, plain, (r2_hidden('#skF_6', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.28/1.52  tff(c_528, plain, (r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_524, c_50])).
% 3.28/1.52  tff(c_607, plain, (![C_188, B_189, A_190]: (~v1_xboole_0(C_188) | ~m1_subset_1(B_189, k1_zfmisc_1(C_188)) | ~r2_hidden(A_190, B_189))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.28/1.52  tff(c_633, plain, (![B_193, A_194, A_195]: (~v1_xboole_0(B_193) | ~r2_hidden(A_194, A_195) | ~r1_tarski(A_195, B_193))), inference(resolution, [status(thm)], [c_14, c_607])).
% 3.28/1.52  tff(c_640, plain, (![B_196]: (~v1_xboole_0(B_196) | ~r1_tarski('#skF_3', B_196))), inference(resolution, [status(thm)], [c_528, c_633])).
% 3.28/1.52  tff(c_645, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_8, c_640])).
% 3.28/1.52  tff(c_42, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.28/1.52  tff(c_48, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.28/1.52  tff(c_535, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_524, c_48])).
% 3.28/1.52  tff(c_52, plain, (r2_hidden('#skF_5', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.28/1.52  tff(c_526, plain, (r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_524, c_52])).
% 3.28/1.52  tff(c_910, plain, (![D_270, C_271, B_272, A_273]: (k1_funct_1(k2_funct_1(D_270), k1_funct_1(D_270, C_271))=C_271 | k1_xboole_0=B_272 | ~r2_hidden(C_271, A_273) | ~v2_funct_1(D_270) | ~m1_subset_1(D_270, k1_zfmisc_1(k2_zfmisc_1(A_273, B_272))) | ~v1_funct_2(D_270, A_273, B_272) | ~v1_funct_1(D_270))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.28/1.52  tff(c_956, plain, (![D_284, B_285]: (k1_funct_1(k2_funct_1(D_284), k1_funct_1(D_284, '#skF_5'))='#skF_5' | k1_xboole_0=B_285 | ~v2_funct_1(D_284) | ~m1_subset_1(D_284, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_285))) | ~v1_funct_2(D_284, '#skF_3', B_285) | ~v1_funct_1(D_284))), inference(resolution, [status(thm)], [c_526, c_910])).
% 3.28/1.52  tff(c_961, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_956])).
% 3.28/1.52  tff(c_965, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_524, c_535, c_961])).
% 3.28/1.52  tff(c_966, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_965])).
% 3.28/1.52  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.28/1.52  tff(c_969, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_966, c_2])).
% 3.28/1.52  tff(c_971, plain, $false, inference(negUnitSimplification, [status(thm)], [c_645, c_969])).
% 3.28/1.52  tff(c_973, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_965])).
% 3.28/1.52  tff(c_523, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_46])).
% 3.28/1.52  tff(c_972, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_965])).
% 3.28/1.52  tff(c_1015, plain, (![D_299, B_300]: (k1_funct_1(k2_funct_1(D_299), k1_funct_1(D_299, '#skF_6'))='#skF_6' | k1_xboole_0=B_300 | ~v2_funct_1(D_299) | ~m1_subset_1(D_299, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_300))) | ~v1_funct_2(D_299, '#skF_3', B_300) | ~v1_funct_1(D_299))), inference(resolution, [status(thm)], [c_528, c_910])).
% 3.28/1.52  tff(c_1020, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_1015])).
% 3.28/1.52  tff(c_1024, plain, ('#skF_5'='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_524, c_972, c_1020])).
% 3.28/1.52  tff(c_1026, plain, $false, inference(negUnitSimplification, [status(thm)], [c_973, c_523, c_1024])).
% 3.28/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.52  
% 3.28/1.52  Inference rules
% 3.28/1.52  ----------------------
% 3.28/1.52  #Ref     : 4
% 3.28/1.52  #Sup     : 182
% 3.28/1.52  #Fact    : 0
% 3.28/1.52  #Define  : 0
% 3.28/1.52  #Split   : 8
% 3.28/1.52  #Chain   : 0
% 3.28/1.52  #Close   : 0
% 3.28/1.52  
% 3.28/1.52  Ordering : KBO
% 3.28/1.52  
% 3.28/1.52  Simplification rules
% 3.28/1.52  ----------------------
% 3.28/1.52  #Subsume      : 23
% 3.28/1.52  #Demod        : 88
% 3.28/1.52  #Tautology    : 36
% 3.28/1.52  #SimpNegUnit  : 10
% 3.28/1.52  #BackRed      : 3
% 3.28/1.52  
% 3.28/1.52  #Partial instantiations: 0
% 3.28/1.52  #Strategies tried      : 1
% 3.28/1.52  
% 3.28/1.52  Timing (in seconds)
% 3.28/1.52  ----------------------
% 3.28/1.52  Preprocessing        : 0.33
% 3.28/1.52  Parsing              : 0.17
% 3.28/1.52  CNF conversion       : 0.02
% 3.28/1.52  Main loop            : 0.43
% 3.28/1.52  Inferencing          : 0.17
% 3.28/1.52  Reduction            : 0.13
% 3.28/1.52  Demodulation         : 0.09
% 3.28/1.52  BG Simplification    : 0.02
% 3.28/1.52  Subsumption          : 0.07
% 3.28/1.52  Abstraction          : 0.02
% 3.28/1.52  MUC search           : 0.00
% 3.28/1.52  Cooper               : 0.00
% 3.28/1.52  Total                : 0.80
% 3.28/1.52  Index Insertion      : 0.00
% 3.28/1.52  Index Deletion       : 0.00
% 3.28/1.52  Index Matching       : 0.00
% 3.28/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
