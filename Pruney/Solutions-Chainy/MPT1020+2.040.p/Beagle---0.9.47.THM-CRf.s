%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:56 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :  137 (2448 expanded)
%              Number of leaves         :   42 ( 808 expanded)
%              Depth                    :   16
%              Number of atoms          :  232 (6215 expanded)
%              Number of equality atoms :   80 (1815 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_183,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & v3_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),k6_partfun1(A))
             => r2_relset_1(A,A,C,k2_funct_2(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_39,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_100,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_40,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( ( k2_relat_1(A) = k1_xboole_0
              & k2_relat_1(B) = k1_xboole_0 )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t197_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_161,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( ( k2_relset_1(A,B,C) = B
              & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
              & v2_funct_1(C) )
           => ( A = k1_xboole_0
              | B = k1_xboole_0
              | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_46,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_696,plain,(
    ! [A_142,B_143,D_144] :
      ( r2_relset_1(A_142,B_143,D_144,D_144)
      | ~ m1_subset_1(D_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_701,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_696])).

tff(c_62,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_127,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_135,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_127])).

tff(c_136,plain,(
    ! [C_50,B_51,A_52] :
      ( v5_relat_1(C_50,B_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_52,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_144,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_136])).

tff(c_703,plain,(
    ! [B_145,A_146] :
      ( k2_relat_1(B_145) = A_146
      | ~ v2_funct_2(B_145,A_146)
      | ~ v5_relat_1(B_145,A_146)
      | ~ v1_relat_1(B_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_709,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_144,c_703])).

tff(c_718,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_709])).

tff(c_722,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_718])).

tff(c_68,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_64,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_902,plain,(
    ! [C_172,B_173,A_174] :
      ( v2_funct_2(C_172,B_173)
      | ~ v3_funct_2(C_172,A_174,B_173)
      | ~ v1_funct_1(C_172)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_174,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_908,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_902])).

tff(c_914,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_908])).

tff(c_916,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_722,c_914])).

tff(c_917,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_718])).

tff(c_4,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_86,plain,(
    ! [A_45] : k6_relat_1(A_45) = k6_partfun1(A_45) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_8,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_92,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_8])).

tff(c_40,plain,(
    ! [A_26] : k6_relat_1(A_26) = k6_partfun1(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_10,plain,(
    ! [A_4] : v1_relat_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_71,plain,(
    ! [A_4] : v1_relat_1(k6_partfun1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_10])).

tff(c_103,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_71])).

tff(c_1045,plain,(
    ! [B_191,A_192] :
      ( B_191 = A_192
      | k2_relat_1(B_191) != k1_xboole_0
      | k2_relat_1(A_192) != k1_xboole_0
      | ~ v1_relat_1(B_191)
      | ~ v1_relat_1(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1051,plain,(
    ! [A_192] :
      ( k1_xboole_0 = A_192
      | k2_relat_1(k1_xboole_0) != k1_xboole_0
      | k2_relat_1(A_192) != k1_xboole_0
      | ~ v1_relat_1(A_192) ) ),
    inference(resolution,[status(thm)],[c_103,c_1045])).

tff(c_1066,plain,(
    ! [A_193] :
      ( k1_xboole_0 = A_193
      | k2_relat_1(A_193) != k1_xboole_0
      | ~ v1_relat_1(A_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1051])).

tff(c_1069,plain,
    ( k1_xboole_0 = '#skF_2'
    | k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_135,c_1066])).

tff(c_1080,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_917,c_1069])).

tff(c_1088,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1080])).

tff(c_66,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_58,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_1030,plain,(
    ! [A_188,B_189,C_190] :
      ( k2_relset_1(A_188,B_189,C_190) = k2_relat_1(C_190)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1036,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_1030])).

tff(c_1040,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_917,c_1036])).

tff(c_1096,plain,(
    ! [C_195,A_196,B_197] :
      ( v2_funct_1(C_195)
      | ~ v3_funct_2(C_195,A_196,B_197)
      | ~ v1_funct_1(C_195)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1102,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_1096])).

tff(c_1108,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_1102])).

tff(c_52,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_1199,plain,(
    ! [C_230,D_231,B_232,A_233] :
      ( k2_funct_1(C_230) = D_231
      | k1_xboole_0 = B_232
      | k1_xboole_0 = A_233
      | ~ v2_funct_1(C_230)
      | ~ r2_relset_1(A_233,A_233,k1_partfun1(A_233,B_232,B_232,A_233,C_230,D_231),k6_partfun1(A_233))
      | k2_relset_1(A_233,B_232,C_230) != B_232
      | ~ m1_subset_1(D_231,k1_zfmisc_1(k2_zfmisc_1(B_232,A_233)))
      | ~ v1_funct_2(D_231,B_232,A_233)
      | ~ v1_funct_1(D_231)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_233,B_232)))
      | ~ v1_funct_2(C_230,A_233,B_232)
      | ~ v1_funct_1(C_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1202,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_1199])).

tff(c_1208,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_62,c_60,c_58,c_54,c_1040,c_1108,c_1202])).

tff(c_1209,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1088,c_1208])).

tff(c_1143,plain,(
    ! [A_207,B_208] :
      ( k2_funct_2(A_207,B_208) = k2_funct_1(B_208)
      | ~ m1_subset_1(B_208,k1_zfmisc_1(k2_zfmisc_1(A_207,A_207)))
      | ~ v3_funct_2(B_208,A_207,A_207)
      | ~ v1_funct_2(B_208,A_207,A_207)
      | ~ v1_funct_1(B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1149,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_1143])).

tff(c_1155,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_1149])).

tff(c_50,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_1160,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1155,c_50])).

tff(c_1211,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1209,c_1160])).

tff(c_1215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_701,c_1211])).

tff(c_1217,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1080])).

tff(c_1216,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1080])).

tff(c_1286,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1217,c_1216])).

tff(c_1241,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1216,c_1216,c_4])).

tff(c_1244,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_917,c_1241])).

tff(c_134,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_127])).

tff(c_143,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_136])).

tff(c_712,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_143,c_703])).

tff(c_721,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_712])).

tff(c_929,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_721])).

tff(c_56,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_1006,plain,(
    ! [C_185,B_186,A_187] :
      ( v2_funct_2(C_185,B_186)
      | ~ v3_funct_2(C_185,A_187,B_186)
      | ~ v1_funct_1(C_185)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_187,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1009,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1006])).

tff(c_1015,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_1009])).

tff(c_1017,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_929,c_1015])).

tff(c_1018,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_721])).

tff(c_1072,plain,
    ( k1_xboole_0 = '#skF_3'
    | k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_134,c_1066])).

tff(c_1082,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1018,c_1072])).

tff(c_1249,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1216,c_1216,c_1082])).

tff(c_1250,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1249])).

tff(c_1283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1244,c_1250])).

tff(c_1284,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1249])).

tff(c_1341,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1286,c_1284])).

tff(c_1353,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1341,c_1341,c_701])).

tff(c_1360,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1341,c_60])).

tff(c_1358,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1341,c_58])).

tff(c_1359,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1341,c_56])).

tff(c_14,plain,(
    ! [A_5] : k2_funct_1(k6_relat_1(A_5)) = k6_relat_1(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_109,plain,(
    ! [A_46] : k2_funct_1(k6_partfun1(A_46)) = k6_partfun1(A_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_14])).

tff(c_118,plain,(
    k6_partfun1(k1_xboole_0) = k2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_109])).

tff(c_121,plain,(
    k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_118])).

tff(c_1235,plain,(
    k2_funct_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1216,c_1216,c_121])).

tff(c_1391,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1286,c_1286,c_1235])).

tff(c_1357,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1341,c_54])).

tff(c_38,plain,(
    ! [A_24,B_25] :
      ( k2_funct_2(A_24,B_25) = k2_funct_1(B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k2_zfmisc_1(A_24,A_24)))
      | ~ v3_funct_2(B_25,A_24,A_24)
      | ~ v1_funct_2(B_25,A_24,A_24)
      | ~ v1_funct_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1424,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1357,c_38])).

tff(c_1447,plain,(
    k2_funct_2('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1360,c_1358,c_1359,c_1391,c_1424])).

tff(c_1320,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1284,c_50])).

tff(c_1464,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1341,c_1341,c_1320])).

tff(c_1465,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1447,c_1464])).

tff(c_1468,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1353,c_1465])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:53:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.60/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.67  
% 3.96/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/1.68  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.96/1.68  
% 3.96/1.68  %Foreground sorts:
% 3.96/1.68  
% 3.96/1.68  
% 3.96/1.68  %Background operators:
% 3.96/1.68  
% 3.96/1.68  
% 3.96/1.68  %Foreground operators:
% 3.96/1.68  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.96/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.96/1.68  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.96/1.68  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.96/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.96/1.68  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.96/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.96/1.68  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 3.96/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.96/1.68  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.96/1.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.96/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.96/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.96/1.68  tff('#skF_1', type, '#skF_1': $i).
% 3.96/1.68  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 3.96/1.68  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.96/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.96/1.68  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.96/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.96/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.96/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.96/1.68  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.96/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.96/1.68  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.96/1.68  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 3.96/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.96/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.96/1.68  
% 4.07/1.70  tff(f_183, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 4.07/1.70  tff(f_68, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.07/1.70  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.07/1.70  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.07/1.70  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 4.07/1.70  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 4.07/1.70  tff(f_39, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.07/1.70  tff(f_100, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.07/1.70  tff(f_40, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 4.07/1.70  tff(f_44, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.07/1.70  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (((k2_relat_1(A) = k1_xboole_0) & (k2_relat_1(B) = k1_xboole_0)) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t197_relat_1)).
% 4.07/1.70  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.07/1.70  tff(f_161, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 4.07/1.70  tff(f_98, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 4.07/1.70  tff(f_46, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 4.07/1.70  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.07/1.70  tff(c_696, plain, (![A_142, B_143, D_144]: (r2_relset_1(A_142, B_143, D_144, D_144) | ~m1_subset_1(D_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.07/1.70  tff(c_701, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_696])).
% 4.07/1.70  tff(c_62, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.07/1.70  tff(c_127, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.07/1.70  tff(c_135, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_127])).
% 4.07/1.70  tff(c_136, plain, (![C_50, B_51, A_52]: (v5_relat_1(C_50, B_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_52, B_51))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.07/1.70  tff(c_144, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_136])).
% 4.07/1.70  tff(c_703, plain, (![B_145, A_146]: (k2_relat_1(B_145)=A_146 | ~v2_funct_2(B_145, A_146) | ~v5_relat_1(B_145, A_146) | ~v1_relat_1(B_145))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.07/1.70  tff(c_709, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_144, c_703])).
% 4.07/1.70  tff(c_718, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_709])).
% 4.07/1.70  tff(c_722, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_718])).
% 4.07/1.70  tff(c_68, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.07/1.70  tff(c_64, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.07/1.70  tff(c_902, plain, (![C_172, B_173, A_174]: (v2_funct_2(C_172, B_173) | ~v3_funct_2(C_172, A_174, B_173) | ~v1_funct_1(C_172) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_174, B_173))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.07/1.70  tff(c_908, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_902])).
% 4.07/1.70  tff(c_914, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_908])).
% 4.07/1.70  tff(c_916, plain, $false, inference(negUnitSimplification, [status(thm)], [c_722, c_914])).
% 4.07/1.70  tff(c_917, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_718])).
% 4.07/1.70  tff(c_4, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.07/1.70  tff(c_86, plain, (![A_45]: (k6_relat_1(A_45)=k6_partfun1(A_45))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.07/1.70  tff(c_8, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.07/1.70  tff(c_92, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_86, c_8])).
% 4.07/1.70  tff(c_40, plain, (![A_26]: (k6_relat_1(A_26)=k6_partfun1(A_26))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.07/1.70  tff(c_10, plain, (![A_4]: (v1_relat_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.07/1.70  tff(c_71, plain, (![A_4]: (v1_relat_1(k6_partfun1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_10])).
% 4.07/1.70  tff(c_103, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_92, c_71])).
% 4.07/1.70  tff(c_1045, plain, (![B_191, A_192]: (B_191=A_192 | k2_relat_1(B_191)!=k1_xboole_0 | k2_relat_1(A_192)!=k1_xboole_0 | ~v1_relat_1(B_191) | ~v1_relat_1(A_192))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.07/1.70  tff(c_1051, plain, (![A_192]: (k1_xboole_0=A_192 | k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k2_relat_1(A_192)!=k1_xboole_0 | ~v1_relat_1(A_192))), inference(resolution, [status(thm)], [c_103, c_1045])).
% 4.07/1.70  tff(c_1066, plain, (![A_193]: (k1_xboole_0=A_193 | k2_relat_1(A_193)!=k1_xboole_0 | ~v1_relat_1(A_193))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1051])).
% 4.07/1.70  tff(c_1069, plain, (k1_xboole_0='#skF_2' | k2_relat_1('#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_135, c_1066])).
% 4.07/1.70  tff(c_1080, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_917, c_1069])).
% 4.07/1.70  tff(c_1088, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_1080])).
% 4.07/1.70  tff(c_66, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.07/1.70  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.07/1.70  tff(c_58, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.07/1.70  tff(c_1030, plain, (![A_188, B_189, C_190]: (k2_relset_1(A_188, B_189, C_190)=k2_relat_1(C_190) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.07/1.70  tff(c_1036, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_1030])).
% 4.07/1.70  tff(c_1040, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_917, c_1036])).
% 4.07/1.70  tff(c_1096, plain, (![C_195, A_196, B_197]: (v2_funct_1(C_195) | ~v3_funct_2(C_195, A_196, B_197) | ~v1_funct_1(C_195) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.07/1.70  tff(c_1102, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_1096])).
% 4.07/1.70  tff(c_1108, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_1102])).
% 4.07/1.70  tff(c_52, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.07/1.70  tff(c_1199, plain, (![C_230, D_231, B_232, A_233]: (k2_funct_1(C_230)=D_231 | k1_xboole_0=B_232 | k1_xboole_0=A_233 | ~v2_funct_1(C_230) | ~r2_relset_1(A_233, A_233, k1_partfun1(A_233, B_232, B_232, A_233, C_230, D_231), k6_partfun1(A_233)) | k2_relset_1(A_233, B_232, C_230)!=B_232 | ~m1_subset_1(D_231, k1_zfmisc_1(k2_zfmisc_1(B_232, A_233))) | ~v1_funct_2(D_231, B_232, A_233) | ~v1_funct_1(D_231) | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_233, B_232))) | ~v1_funct_2(C_230, A_233, B_232) | ~v1_funct_1(C_230))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.07/1.70  tff(c_1202, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_52, c_1199])).
% 4.07/1.70  tff(c_1208, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_62, c_60, c_58, c_54, c_1040, c_1108, c_1202])).
% 4.07/1.70  tff(c_1209, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1088, c_1208])).
% 4.07/1.70  tff(c_1143, plain, (![A_207, B_208]: (k2_funct_2(A_207, B_208)=k2_funct_1(B_208) | ~m1_subset_1(B_208, k1_zfmisc_1(k2_zfmisc_1(A_207, A_207))) | ~v3_funct_2(B_208, A_207, A_207) | ~v1_funct_2(B_208, A_207, A_207) | ~v1_funct_1(B_208))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.07/1.70  tff(c_1149, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_1143])).
% 4.07/1.70  tff(c_1155, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_1149])).
% 4.07/1.70  tff(c_50, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.07/1.70  tff(c_1160, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1155, c_50])).
% 4.07/1.70  tff(c_1211, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1209, c_1160])).
% 4.07/1.70  tff(c_1215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_701, c_1211])).
% 4.07/1.70  tff(c_1217, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_1080])).
% 4.07/1.70  tff(c_1216, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1080])).
% 4.07/1.70  tff(c_1286, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1217, c_1216])).
% 4.07/1.70  tff(c_1241, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1216, c_1216, c_4])).
% 4.07/1.70  tff(c_1244, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_917, c_1241])).
% 4.07/1.70  tff(c_134, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_127])).
% 4.07/1.70  tff(c_143, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_136])).
% 4.07/1.70  tff(c_712, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_143, c_703])).
% 4.07/1.70  tff(c_721, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_712])).
% 4.07/1.70  tff(c_929, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_721])).
% 4.07/1.70  tff(c_56, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_183])).
% 4.07/1.70  tff(c_1006, plain, (![C_185, B_186, A_187]: (v2_funct_2(C_185, B_186) | ~v3_funct_2(C_185, A_187, B_186) | ~v1_funct_1(C_185) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_187, B_186))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.07/1.70  tff(c_1009, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_1006])).
% 4.07/1.70  tff(c_1015, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_1009])).
% 4.07/1.70  tff(c_1017, plain, $false, inference(negUnitSimplification, [status(thm)], [c_929, c_1015])).
% 4.07/1.70  tff(c_1018, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_721])).
% 4.07/1.70  tff(c_1072, plain, (k1_xboole_0='#skF_3' | k2_relat_1('#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_134, c_1066])).
% 4.07/1.70  tff(c_1082, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1018, c_1072])).
% 4.07/1.70  tff(c_1249, plain, ('#skF_2'='#skF_3' | '#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1216, c_1216, c_1082])).
% 4.07/1.70  tff(c_1250, plain, ('#skF_2'!='#skF_1'), inference(splitLeft, [status(thm)], [c_1249])).
% 4.07/1.70  tff(c_1283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1244, c_1250])).
% 4.07/1.70  tff(c_1284, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_1249])).
% 4.07/1.70  tff(c_1341, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1286, c_1284])).
% 4.07/1.70  tff(c_1353, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1341, c_1341, c_701])).
% 4.07/1.70  tff(c_1360, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1341, c_60])).
% 4.07/1.70  tff(c_1358, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1341, c_58])).
% 4.07/1.70  tff(c_1359, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1341, c_56])).
% 4.07/1.70  tff(c_14, plain, (![A_5]: (k2_funct_1(k6_relat_1(A_5))=k6_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.07/1.70  tff(c_109, plain, (![A_46]: (k2_funct_1(k6_partfun1(A_46))=k6_partfun1(A_46))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_14])).
% 4.07/1.70  tff(c_118, plain, (k6_partfun1(k1_xboole_0)=k2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_92, c_109])).
% 4.07/1.70  tff(c_121, plain, (k2_funct_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_92, c_118])).
% 4.07/1.70  tff(c_1235, plain, (k2_funct_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1216, c_1216, c_121])).
% 4.07/1.70  tff(c_1391, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1286, c_1286, c_1235])).
% 4.07/1.70  tff(c_1357, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1341, c_54])).
% 4.07/1.70  tff(c_38, plain, (![A_24, B_25]: (k2_funct_2(A_24, B_25)=k2_funct_1(B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))) | ~v3_funct_2(B_25, A_24, A_24) | ~v1_funct_2(B_25, A_24, A_24) | ~v1_funct_1(B_25))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.07/1.70  tff(c_1424, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_1357, c_38])).
% 4.07/1.70  tff(c_1447, plain, (k2_funct_2('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1360, c_1358, c_1359, c_1391, c_1424])).
% 4.07/1.70  tff(c_1320, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1284, c_50])).
% 4.07/1.70  tff(c_1464, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1341, c_1341, c_1320])).
% 4.07/1.70  tff(c_1465, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1447, c_1464])).
% 4.07/1.70  tff(c_1468, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1353, c_1465])).
% 4.07/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.07/1.70  
% 4.07/1.70  Inference rules
% 4.07/1.70  ----------------------
% 4.07/1.70  #Ref     : 0
% 4.07/1.70  #Sup     : 289
% 4.07/1.70  #Fact    : 0
% 4.07/1.70  #Define  : 0
% 4.07/1.70  #Split   : 23
% 4.07/1.70  #Chain   : 0
% 4.07/1.70  #Close   : 0
% 4.07/1.70  
% 4.07/1.70  Ordering : KBO
% 4.07/1.70  
% 4.07/1.70  Simplification rules
% 4.07/1.70  ----------------------
% 4.07/1.70  #Subsume      : 20
% 4.07/1.70  #Demod        : 458
% 4.07/1.70  #Tautology    : 190
% 4.07/1.70  #SimpNegUnit  : 7
% 4.07/1.70  #BackRed      : 97
% 4.07/1.70  
% 4.07/1.70  #Partial instantiations: 0
% 4.07/1.70  #Strategies tried      : 1
% 4.07/1.70  
% 4.07/1.70  Timing (in seconds)
% 4.07/1.70  ----------------------
% 4.07/1.70  Preprocessing        : 0.37
% 4.07/1.70  Parsing              : 0.21
% 4.07/1.70  CNF conversion       : 0.02
% 4.07/1.70  Main loop            : 0.50
% 4.07/1.70  Inferencing          : 0.16
% 4.07/1.70  Reduction            : 0.18
% 4.07/1.70  Demodulation         : 0.13
% 4.07/1.70  BG Simplification    : 0.02
% 4.07/1.70  Subsumption          : 0.08
% 4.07/1.70  Abstraction          : 0.02
% 4.07/1.70  MUC search           : 0.00
% 4.07/1.70  Cooper               : 0.00
% 4.07/1.70  Total                : 0.92
% 4.07/1.70  Index Insertion      : 0.00
% 4.07/1.70  Index Deletion       : 0.00
% 4.07/1.70  Index Matching       : 0.00
% 4.07/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
