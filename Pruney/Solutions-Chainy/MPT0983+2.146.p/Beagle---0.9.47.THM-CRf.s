%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:22 EST 2020

% Result     : Theorem 7.16s
% Output     : CNFRefutation 7.16s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 246 expanded)
%              Number of leaves         :   45 ( 105 expanded)
%              Depth                    :    9
%              Number of atoms          :  212 ( 732 expanded)
%              Number of equality atoms :   41 (  64 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_163,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_104,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_45,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_74,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_84,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_143,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_43,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_133,plain,(
    ! [C_77,A_78,B_79] :
      ( v1_xboole_0(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ v1_xboole_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_145,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_133])).

tff(c_147,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_44,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_72,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_56,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_50,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_36,plain,(
    ! [A_44] : k6_relat_1(A_44) = k6_partfun1(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_10,plain,(
    ! [A_8] : v2_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_60,plain,(
    ! [A_8] : v2_funct_1(k6_partfun1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_10])).

tff(c_1349,plain,(
    ! [F_174,D_171,C_173,B_175,A_172,E_176] :
      ( k4_relset_1(A_172,B_175,C_173,D_171,E_176,F_174) = k5_relat_1(E_176,F_174)
      | ~ m1_subset_1(F_174,k1_zfmisc_1(k2_zfmisc_1(C_173,D_171)))
      | ~ m1_subset_1(E_176,k1_zfmisc_1(k2_zfmisc_1(A_172,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1844,plain,(
    ! [A_195,B_196,E_197] :
      ( k4_relset_1(A_195,B_196,'#skF_2','#skF_1',E_197,'#skF_4') = k5_relat_1(E_197,'#skF_4')
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196))) ) ),
    inference(resolution,[status(thm)],[c_48,c_1349])).

tff(c_1872,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_1844])).

tff(c_18,plain,(
    ! [C_18,B_17,A_16,D_19,E_20,F_21] :
      ( m1_subset_1(k4_relset_1(A_16,B_17,C_18,D_19,E_20,F_21),k1_zfmisc_1(k2_zfmisc_1(A_16,D_19)))
      | ~ m1_subset_1(F_21,k1_zfmisc_1(k2_zfmisc_1(C_18,D_19)))
      | ~ m1_subset_1(E_20,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2014,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1872,c_18])).

tff(c_2018,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_2014])).

tff(c_1915,plain,(
    ! [B_199,E_200,D_203,C_202,A_198,F_201] :
      ( k1_partfun1(A_198,B_199,C_202,D_203,E_200,F_201) = k5_relat_1(E_200,F_201)
      | ~ m1_subset_1(F_201,k1_zfmisc_1(k2_zfmisc_1(C_202,D_203)))
      | ~ v1_funct_1(F_201)
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199)))
      | ~ v1_funct_1(E_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1929,plain,(
    ! [A_198,B_199,E_200] :
      ( k1_partfun1(A_198,B_199,'#skF_2','#skF_1',E_200,'#skF_4') = k5_relat_1(E_200,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_198,B_199)))
      | ~ v1_funct_1(E_200) ) ),
    inference(resolution,[status(thm)],[c_48,c_1915])).

tff(c_2930,plain,(
    ! [A_234,B_235,E_236] :
      ( k1_partfun1(A_234,B_235,'#skF_2','#skF_1',E_236,'#skF_4') = k5_relat_1(E_236,'#skF_4')
      | ~ m1_subset_1(E_236,k1_zfmisc_1(k2_zfmisc_1(A_234,B_235)))
      | ~ v1_funct_1(E_236) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1929])).

tff(c_2969,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_2930])).

tff(c_2990,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2969])).

tff(c_28,plain,(
    ! [A_35] : m1_subset_1(k6_relat_1(A_35),k1_zfmisc_1(k2_zfmisc_1(A_35,A_35))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_59,plain,(
    ! [A_35] : m1_subset_1(k6_partfun1(A_35),k1_zfmisc_1(k2_zfmisc_1(A_35,A_35))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28])).

tff(c_46,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_1198,plain,(
    ! [D_156,C_157,A_158,B_159] :
      ( D_156 = C_157
      | ~ r2_relset_1(A_158,B_159,C_157,D_156)
      | ~ m1_subset_1(D_156,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159)))
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1208,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_46,c_1198])).

tff(c_1227,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_1208])).

tff(c_1259,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1227])).

tff(c_4507,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2990,c_1259])).

tff(c_4511,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2018,c_4507])).

tff(c_4512,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1227])).

tff(c_5405,plain,(
    ! [C_354,E_353,B_355,A_352,D_356] :
      ( k1_xboole_0 = C_354
      | v2_funct_1(D_356)
      | ~ v2_funct_1(k1_partfun1(A_352,B_355,B_355,C_354,D_356,E_353))
      | ~ m1_subset_1(E_353,k1_zfmisc_1(k2_zfmisc_1(B_355,C_354)))
      | ~ v1_funct_2(E_353,B_355,C_354)
      | ~ v1_funct_1(E_353)
      | ~ m1_subset_1(D_356,k1_zfmisc_1(k2_zfmisc_1(A_352,B_355)))
      | ~ v1_funct_2(D_356,A_352,B_355)
      | ~ v1_funct_1(D_356) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_5407,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4512,c_5405])).

tff(c_5409,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_50,c_48,c_60,c_5407])).

tff(c_5410,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_5409])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_5439,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5410,c_2])).

tff(c_5441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_5439])).

tff(c_5443,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_73,plain,(
    ! [B_61,A_62] :
      ( ~ v1_xboole_0(B_61)
      | B_61 = A_62
      | ~ v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_76,plain,(
    ! [A_62] :
      ( k1_xboole_0 = A_62
      | ~ v1_xboole_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_2,c_73])).

tff(c_5456,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_5443,c_76])).

tff(c_5442,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_5449,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5442,c_76])).

tff(c_5465,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5456,c_5449])).

tff(c_5475,plain,(
    ~ v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5465,c_72])).

tff(c_5511,plain,(
    ! [A_360] :
      ( v1_xboole_0(k6_partfun1(A_360))
      | ~ v1_xboole_0(A_360) ) ),
    inference(resolution,[status(thm)],[c_59,c_133])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_5457,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_5443,c_4])).

tff(c_5519,plain,(
    ! [A_361] :
      ( k6_partfun1(A_361) = '#skF_1'
      | ~ v1_xboole_0(A_361) ) ),
    inference(resolution,[status(thm)],[c_5511,c_5457])).

tff(c_5527,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_5443,c_5519])).

tff(c_5544,plain,(
    v2_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5527,c_60])).

tff(c_5552,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5475,c_5544])).

tff(c_5553,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5566,plain,(
    ! [B_366,A_367] :
      ( v1_relat_1(B_366)
      | ~ m1_subset_1(B_366,k1_zfmisc_1(A_367))
      | ~ v1_relat_1(A_367) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5575,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_48,c_5566])).

tff(c_5584,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_5575])).

tff(c_5585,plain,(
    ! [C_368,B_369,A_370] :
      ( v5_relat_1(C_368,B_369)
      | ~ m1_subset_1(C_368,k1_zfmisc_1(k2_zfmisc_1(A_370,B_369))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5597,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_5585])).

tff(c_5797,plain,(
    ! [A_391,B_392,C_393] :
      ( k2_relset_1(A_391,B_392,C_393) = k2_relat_1(C_393)
      | ~ m1_subset_1(C_393,k1_zfmisc_1(k2_zfmisc_1(A_391,B_392))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5813,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_5797])).

tff(c_6834,plain,(
    ! [A_449,B_450,C_451,D_452] :
      ( k2_relset_1(A_449,B_450,C_451) = B_450
      | ~ r2_relset_1(B_450,B_450,k1_partfun1(B_450,A_449,A_449,B_450,D_452,C_451),k6_partfun1(B_450))
      | ~ m1_subset_1(D_452,k1_zfmisc_1(k2_zfmisc_1(B_450,A_449)))
      | ~ v1_funct_2(D_452,B_450,A_449)
      | ~ v1_funct_1(D_452)
      | ~ m1_subset_1(C_451,k1_zfmisc_1(k2_zfmisc_1(A_449,B_450)))
      | ~ v1_funct_2(C_451,A_449,B_450)
      | ~ v1_funct_1(C_451) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_6849,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_6834])).

tff(c_6852,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_58,c_56,c_54,c_5813,c_6849])).

tff(c_30,plain,(
    ! [B_37] :
      ( v2_funct_2(B_37,k2_relat_1(B_37))
      | ~ v5_relat_1(B_37,k2_relat_1(B_37))
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6857,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6852,c_30])).

tff(c_6861,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5584,c_5597,c_6852,c_6857])).

tff(c_6863,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5553,c_6861])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:31:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.16/2.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.16/2.47  
% 7.16/2.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.16/2.48  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.16/2.48  
% 7.16/2.48  %Foreground sorts:
% 7.16/2.48  
% 7.16/2.48  
% 7.16/2.48  %Background operators:
% 7.16/2.48  
% 7.16/2.48  
% 7.16/2.48  %Foreground operators:
% 7.16/2.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.16/2.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.16/2.48  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.16/2.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.16/2.48  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.16/2.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.16/2.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.16/2.48  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.16/2.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.16/2.48  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.16/2.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.16/2.48  tff('#skF_2', type, '#skF_2': $i).
% 7.16/2.48  tff('#skF_3', type, '#skF_3': $i).
% 7.16/2.48  tff('#skF_1', type, '#skF_1': $i).
% 7.16/2.48  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.16/2.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.16/2.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.16/2.48  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.16/2.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.16/2.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.16/2.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.16/2.48  tff('#skF_4', type, '#skF_4': $i).
% 7.16/2.48  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.16/2.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.16/2.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.16/2.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.16/2.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.16/2.48  
% 7.16/2.51  tff(f_163, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 7.16/2.51  tff(f_58, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 7.16/2.51  tff(f_104, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.16/2.51  tff(f_45, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 7.16/2.51  tff(f_74, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 7.16/2.51  tff(f_64, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 7.16/2.51  tff(f_102, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.16/2.51  tff(f_84, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 7.16/2.51  tff(f_82, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.16/2.51  tff(f_143, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 7.16/2.51  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.16/2.51  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 7.16/2.51  tff(f_43, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.16/2.51  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.16/2.51  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.16/2.51  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.16/2.51  tff(f_121, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 7.16/2.51  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 7.16/2.51  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.16/2.51  tff(c_133, plain, (![C_77, A_78, B_79]: (v1_xboole_0(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~v1_xboole_0(A_78))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.16/2.51  tff(c_145, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_133])).
% 7.16/2.51  tff(c_147, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_145])).
% 7.16/2.51  tff(c_44, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.16/2.51  tff(c_72, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 7.16/2.51  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.16/2.51  tff(c_56, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.16/2.51  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.16/2.51  tff(c_50, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.16/2.51  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.16/2.51  tff(c_36, plain, (![A_44]: (k6_relat_1(A_44)=k6_partfun1(A_44))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.16/2.51  tff(c_10, plain, (![A_8]: (v2_funct_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.16/2.51  tff(c_60, plain, (![A_8]: (v2_funct_1(k6_partfun1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_10])).
% 7.16/2.51  tff(c_1349, plain, (![F_174, D_171, C_173, B_175, A_172, E_176]: (k4_relset_1(A_172, B_175, C_173, D_171, E_176, F_174)=k5_relat_1(E_176, F_174) | ~m1_subset_1(F_174, k1_zfmisc_1(k2_zfmisc_1(C_173, D_171))) | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(A_172, B_175))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.16/2.51  tff(c_1844, plain, (![A_195, B_196, E_197]: (k4_relset_1(A_195, B_196, '#skF_2', '#skF_1', E_197, '#skF_4')=k5_relat_1(E_197, '#skF_4') | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))))), inference(resolution, [status(thm)], [c_48, c_1349])).
% 7.16/2.51  tff(c_1872, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_1844])).
% 7.16/2.51  tff(c_18, plain, (![C_18, B_17, A_16, D_19, E_20, F_21]: (m1_subset_1(k4_relset_1(A_16, B_17, C_18, D_19, E_20, F_21), k1_zfmisc_1(k2_zfmisc_1(A_16, D_19))) | ~m1_subset_1(F_21, k1_zfmisc_1(k2_zfmisc_1(C_18, D_19))) | ~m1_subset_1(E_20, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.16/2.51  tff(c_2014, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1872, c_18])).
% 7.16/2.51  tff(c_2018, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48, c_2014])).
% 7.16/2.51  tff(c_1915, plain, (![B_199, E_200, D_203, C_202, A_198, F_201]: (k1_partfun1(A_198, B_199, C_202, D_203, E_200, F_201)=k5_relat_1(E_200, F_201) | ~m1_subset_1(F_201, k1_zfmisc_1(k2_zfmisc_1(C_202, D_203))) | ~v1_funct_1(F_201) | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))) | ~v1_funct_1(E_200))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.16/2.51  tff(c_1929, plain, (![A_198, B_199, E_200]: (k1_partfun1(A_198, B_199, '#skF_2', '#skF_1', E_200, '#skF_4')=k5_relat_1(E_200, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(A_198, B_199))) | ~v1_funct_1(E_200))), inference(resolution, [status(thm)], [c_48, c_1915])).
% 7.16/2.51  tff(c_2930, plain, (![A_234, B_235, E_236]: (k1_partfun1(A_234, B_235, '#skF_2', '#skF_1', E_236, '#skF_4')=k5_relat_1(E_236, '#skF_4') | ~m1_subset_1(E_236, k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))) | ~v1_funct_1(E_236))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1929])).
% 7.16/2.51  tff(c_2969, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_2930])).
% 7.16/2.51  tff(c_2990, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2969])).
% 7.16/2.51  tff(c_28, plain, (![A_35]: (m1_subset_1(k6_relat_1(A_35), k1_zfmisc_1(k2_zfmisc_1(A_35, A_35))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.16/2.51  tff(c_59, plain, (![A_35]: (m1_subset_1(k6_partfun1(A_35), k1_zfmisc_1(k2_zfmisc_1(A_35, A_35))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_28])).
% 7.16/2.51  tff(c_46, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.16/2.51  tff(c_1198, plain, (![D_156, C_157, A_158, B_159]: (D_156=C_157 | ~r2_relset_1(A_158, B_159, C_157, D_156) | ~m1_subset_1(D_156, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.16/2.51  tff(c_1208, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_46, c_1198])).
% 7.16/2.51  tff(c_1227, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_1208])).
% 7.16/2.51  tff(c_1259, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1227])).
% 7.16/2.51  tff(c_4507, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2990, c_1259])).
% 7.16/2.51  tff(c_4511, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2018, c_4507])).
% 7.16/2.51  tff(c_4512, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1227])).
% 7.16/2.51  tff(c_5405, plain, (![C_354, E_353, B_355, A_352, D_356]: (k1_xboole_0=C_354 | v2_funct_1(D_356) | ~v2_funct_1(k1_partfun1(A_352, B_355, B_355, C_354, D_356, E_353)) | ~m1_subset_1(E_353, k1_zfmisc_1(k2_zfmisc_1(B_355, C_354))) | ~v1_funct_2(E_353, B_355, C_354) | ~v1_funct_1(E_353) | ~m1_subset_1(D_356, k1_zfmisc_1(k2_zfmisc_1(A_352, B_355))) | ~v1_funct_2(D_356, A_352, B_355) | ~v1_funct_1(D_356))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.16/2.51  tff(c_5407, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4512, c_5405])).
% 7.16/2.51  tff(c_5409, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_50, c_48, c_60, c_5407])).
% 7.16/2.51  tff(c_5410, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_72, c_5409])).
% 7.16/2.51  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.16/2.51  tff(c_5439, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5410, c_2])).
% 7.16/2.51  tff(c_5441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_5439])).
% 7.16/2.51  tff(c_5443, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_145])).
% 7.16/2.51  tff(c_73, plain, (![B_61, A_62]: (~v1_xboole_0(B_61) | B_61=A_62 | ~v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.16/2.51  tff(c_76, plain, (![A_62]: (k1_xboole_0=A_62 | ~v1_xboole_0(A_62))), inference(resolution, [status(thm)], [c_2, c_73])).
% 7.16/2.51  tff(c_5456, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_5443, c_76])).
% 7.16/2.51  tff(c_5442, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_145])).
% 7.16/2.51  tff(c_5449, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_5442, c_76])).
% 7.16/2.51  tff(c_5465, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5456, c_5449])).
% 7.16/2.51  tff(c_5475, plain, (~v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5465, c_72])).
% 7.16/2.51  tff(c_5511, plain, (![A_360]: (v1_xboole_0(k6_partfun1(A_360)) | ~v1_xboole_0(A_360))), inference(resolution, [status(thm)], [c_59, c_133])).
% 7.16/2.51  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.16/2.51  tff(c_5457, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_5443, c_4])).
% 7.16/2.51  tff(c_5519, plain, (![A_361]: (k6_partfun1(A_361)='#skF_1' | ~v1_xboole_0(A_361))), inference(resolution, [status(thm)], [c_5511, c_5457])).
% 7.16/2.51  tff(c_5527, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_5443, c_5519])).
% 7.16/2.51  tff(c_5544, plain, (v2_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5527, c_60])).
% 7.16/2.51  tff(c_5552, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5475, c_5544])).
% 7.16/2.51  tff(c_5553, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 7.16/2.51  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.16/2.51  tff(c_5566, plain, (![B_366, A_367]: (v1_relat_1(B_366) | ~m1_subset_1(B_366, k1_zfmisc_1(A_367)) | ~v1_relat_1(A_367))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.16/2.51  tff(c_5575, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_48, c_5566])).
% 7.16/2.51  tff(c_5584, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_5575])).
% 7.16/2.51  tff(c_5585, plain, (![C_368, B_369, A_370]: (v5_relat_1(C_368, B_369) | ~m1_subset_1(C_368, k1_zfmisc_1(k2_zfmisc_1(A_370, B_369))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.16/2.51  tff(c_5597, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_5585])).
% 7.16/2.51  tff(c_5797, plain, (![A_391, B_392, C_393]: (k2_relset_1(A_391, B_392, C_393)=k2_relat_1(C_393) | ~m1_subset_1(C_393, k1_zfmisc_1(k2_zfmisc_1(A_391, B_392))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.16/2.51  tff(c_5813, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_5797])).
% 7.16/2.51  tff(c_6834, plain, (![A_449, B_450, C_451, D_452]: (k2_relset_1(A_449, B_450, C_451)=B_450 | ~r2_relset_1(B_450, B_450, k1_partfun1(B_450, A_449, A_449, B_450, D_452, C_451), k6_partfun1(B_450)) | ~m1_subset_1(D_452, k1_zfmisc_1(k2_zfmisc_1(B_450, A_449))) | ~v1_funct_2(D_452, B_450, A_449) | ~v1_funct_1(D_452) | ~m1_subset_1(C_451, k1_zfmisc_1(k2_zfmisc_1(A_449, B_450))) | ~v1_funct_2(C_451, A_449, B_450) | ~v1_funct_1(C_451))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.16/2.51  tff(c_6849, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_6834])).
% 7.16/2.51  tff(c_6852, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_58, c_56, c_54, c_5813, c_6849])).
% 7.16/2.51  tff(c_30, plain, (![B_37]: (v2_funct_2(B_37, k2_relat_1(B_37)) | ~v5_relat_1(B_37, k2_relat_1(B_37)) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.16/2.51  tff(c_6857, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6852, c_30])).
% 7.16/2.51  tff(c_6861, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5584, c_5597, c_6852, c_6857])).
% 7.16/2.51  tff(c_6863, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5553, c_6861])).
% 7.16/2.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.16/2.51  
% 7.16/2.51  Inference rules
% 7.16/2.52  ----------------------
% 7.16/2.52  #Ref     : 0
% 7.16/2.52  #Sup     : 1750
% 7.16/2.52  #Fact    : 0
% 7.16/2.52  #Define  : 0
% 7.16/2.52  #Split   : 20
% 7.16/2.52  #Chain   : 0
% 7.16/2.52  #Close   : 0
% 7.16/2.52  
% 7.16/2.52  Ordering : KBO
% 7.16/2.52  
% 7.16/2.52  Simplification rules
% 7.16/2.52  ----------------------
% 7.16/2.52  #Subsume      : 162
% 7.16/2.52  #Demod        : 1008
% 7.16/2.52  #Tautology    : 485
% 7.16/2.52  #SimpNegUnit  : 5
% 7.16/2.52  #BackRed      : 66
% 7.16/2.52  
% 7.16/2.52  #Partial instantiations: 0
% 7.16/2.52  #Strategies tried      : 1
% 7.16/2.52  
% 7.16/2.52  Timing (in seconds)
% 7.16/2.52  ----------------------
% 7.16/2.52  Preprocessing        : 0.35
% 7.16/2.52  Parsing              : 0.19
% 7.16/2.52  CNF conversion       : 0.02
% 7.16/2.52  Main loop            : 1.35
% 7.16/2.52  Inferencing          : 0.42
% 7.16/2.52  Reduction            : 0.50
% 7.16/2.52  Demodulation         : 0.37
% 7.16/2.52  BG Simplification    : 0.05
% 7.16/2.52  Subsumption          : 0.26
% 7.16/2.52  Abstraction          : 0.06
% 7.16/2.52  MUC search           : 0.00
% 7.16/2.52  Cooper               : 0.00
% 7.16/2.52  Total                : 1.77
% 7.16/2.52  Index Insertion      : 0.00
% 7.16/2.52  Index Deletion       : 0.00
% 7.16/2.52  Index Matching       : 0.00
% 7.16/2.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
