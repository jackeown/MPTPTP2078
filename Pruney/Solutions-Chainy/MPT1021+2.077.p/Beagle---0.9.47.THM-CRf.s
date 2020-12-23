%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:12 EST 2020

% Result     : Theorem 5.06s
% Output     : CNFRefutation 5.06s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 356 expanded)
%              Number of leaves         :   41 ( 152 expanded)
%              Depth                    :    9
%              Number of atoms          :  265 (1077 expanded)
%              Number of equality atoms :   41 (  88 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_143,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_122,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_64,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_120,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_110,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_130,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_71,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_77,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_50,c_71])).

tff(c_83,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_77])).

tff(c_56,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_52,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1948,plain,(
    ! [C_199,A_200,B_201] :
      ( v2_funct_1(C_199)
      | ~ v3_funct_2(C_199,A_200,B_201)
      | ~ v1_funct_1(C_199)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1954,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1948])).

tff(c_1958,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_1954])).

tff(c_44,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_20,plain,(
    ! [A_17] : m1_subset_1(k6_relat_1(A_17),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_57,plain,(
    ! [A_17] : m1_subset_1(k6_partfun1(A_17),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_20])).

tff(c_1807,plain,(
    ! [A_172,B_173,D_174] :
      ( r2_relset_1(A_172,B_173,D_174,D_174)
      | ~ m1_subset_1(D_174,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1812,plain,(
    ! [A_17] : r2_relset_1(A_17,A_17,k6_partfun1(A_17),k6_partfun1(A_17)) ),
    inference(resolution,[status(thm)],[c_57,c_1807])).

tff(c_1786,plain,(
    ! [C_163,B_164,A_165] :
      ( v5_relat_1(C_163,B_164)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_165,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1794,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1786])).

tff(c_1815,plain,(
    ! [B_176,A_177] :
      ( k2_relat_1(B_176) = A_177
      | ~ v2_funct_2(B_176,A_177)
      | ~ v5_relat_1(B_176,A_177)
      | ~ v1_relat_1(B_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1821,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1794,c_1815])).

tff(c_1827,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_1821])).

tff(c_1828,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1827])).

tff(c_1882,plain,(
    ! [C_189,B_190,A_191] :
      ( v2_funct_2(C_189,B_190)
      | ~ v3_funct_2(C_189,A_191,B_190)
      | ~ v1_funct_1(C_189)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_191,B_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1888,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1882])).

tff(c_1892,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_1888])).

tff(c_1894,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1828,c_1892])).

tff(c_1895,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1827])).

tff(c_6,plain,(
    ! [A_6] :
      ( k5_relat_1(k2_funct_1(A_6),A_6) = k6_relat_1(k2_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_59,plain,(
    ! [A_6] :
      ( k5_relat_1(k2_funct_1(A_6),A_6) = k6_partfun1(k2_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6])).

tff(c_54,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2025,plain,(
    ! [A_217,B_218] :
      ( k2_funct_2(A_217,B_218) = k2_funct_1(B_218)
      | ~ m1_subset_1(B_218,k1_zfmisc_1(k2_zfmisc_1(A_217,A_217)))
      | ~ v3_funct_2(B_218,A_217,A_217)
      | ~ v1_funct_2(B_218,A_217,A_217)
      | ~ v1_funct_1(B_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2031,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_2025])).

tff(c_2035,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2031])).

tff(c_2013,plain,(
    ! [A_214,B_215] :
      ( v1_funct_1(k2_funct_2(A_214,B_215))
      | ~ m1_subset_1(B_215,k1_zfmisc_1(k2_zfmisc_1(A_214,A_214)))
      | ~ v3_funct_2(B_215,A_214,A_214)
      | ~ v1_funct_2(B_215,A_214,A_214)
      | ~ v1_funct_1(B_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2019,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_2013])).

tff(c_2023,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2019])).

tff(c_2045,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2035,c_2023])).

tff(c_32,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(k2_funct_2(A_23,B_24),k1_zfmisc_1(k2_zfmisc_1(A_23,A_23)))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k2_zfmisc_1(A_23,A_23)))
      | ~ v3_funct_2(B_24,A_23,A_23)
      | ~ v1_funct_2(B_24,A_23,A_23)
      | ~ v1_funct_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2190,plain,(
    ! [D_227,A_228,C_229,E_232,B_231,F_230] :
      ( k1_partfun1(A_228,B_231,C_229,D_227,E_232,F_230) = k5_relat_1(E_232,F_230)
      | ~ m1_subset_1(F_230,k1_zfmisc_1(k2_zfmisc_1(C_229,D_227)))
      | ~ v1_funct_1(F_230)
      | ~ m1_subset_1(E_232,k1_zfmisc_1(k2_zfmisc_1(A_228,B_231)))
      | ~ v1_funct_1(E_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2198,plain,(
    ! [A_228,B_231,E_232] :
      ( k1_partfun1(A_228,B_231,'#skF_1','#skF_1',E_232,'#skF_2') = k5_relat_1(E_232,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_232,k1_zfmisc_1(k2_zfmisc_1(A_228,B_231)))
      | ~ v1_funct_1(E_232) ) ),
    inference(resolution,[status(thm)],[c_50,c_2190])).

tff(c_2217,plain,(
    ! [A_233,B_234,E_235] :
      ( k1_partfun1(A_233,B_234,'#skF_1','#skF_1',E_235,'#skF_2') = k5_relat_1(E_235,'#skF_2')
      | ~ m1_subset_1(E_235,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234)))
      | ~ v1_funct_1(E_235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2198])).

tff(c_2436,plain,(
    ! [A_242,B_243] :
      ( k1_partfun1(A_242,A_242,'#skF_1','#skF_1',k2_funct_2(A_242,B_243),'#skF_2') = k5_relat_1(k2_funct_2(A_242,B_243),'#skF_2')
      | ~ v1_funct_1(k2_funct_2(A_242,B_243))
      | ~ m1_subset_1(B_243,k1_zfmisc_1(k2_zfmisc_1(A_242,A_242)))
      | ~ v3_funct_2(B_243,A_242,A_242)
      | ~ v1_funct_2(B_243,A_242,A_242)
      | ~ v1_funct_1(B_243) ) ),
    inference(resolution,[status(thm)],[c_32,c_2217])).

tff(c_2446,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2') = k5_relat_1(k2_funct_2('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_2436])).

tff(c_2457,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2') = k5_relat_1(k2_funct_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_2045,c_2035,c_2035,c_2035,c_2446])).

tff(c_256,plain,(
    ! [C_83,A_84,B_85] :
      ( v2_funct_1(C_83)
      | ~ v3_funct_2(C_83,A_84,B_85)
      | ~ v1_funct_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_262,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_256])).

tff(c_266,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_262])).

tff(c_197,plain,(
    ! [A_72,B_73,D_74] :
      ( r2_relset_1(A_72,B_73,D_74,D_74)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_202,plain,(
    ! [A_17] : r2_relset_1(A_17,A_17,k6_partfun1(A_17),k6_partfun1(A_17)) ),
    inference(resolution,[status(thm)],[c_57,c_197])).

tff(c_216,plain,(
    ! [A_77,B_78,C_79] :
      ( k1_relset_1(A_77,B_78,C_79) = k1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_224,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_216])).

tff(c_280,plain,(
    ! [A_91,B_92] :
      ( k1_relset_1(A_91,A_91,B_92) = A_91
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k2_zfmisc_1(A_91,A_91)))
      | ~ v1_funct_2(B_92,A_91,A_91)
      | ~ v1_funct_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_286,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_280])).

tff(c_291,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_224,c_286])).

tff(c_8,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k2_funct_1(A_6)) = k6_relat_1(k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_58,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k2_funct_1(A_6)) = k6_partfun1(k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_8])).

tff(c_326,plain,(
    ! [A_100,B_101] :
      ( k2_funct_2(A_100,B_101) = k2_funct_1(B_101)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(k2_zfmisc_1(A_100,A_100)))
      | ~ v3_funct_2(B_101,A_100,A_100)
      | ~ v1_funct_2(B_101,A_100,A_100)
      | ~ v1_funct_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_332,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_326])).

tff(c_336,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_332])).

tff(c_315,plain,(
    ! [A_98,B_99] :
      ( v1_funct_1(k2_funct_2(A_98,B_99))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(k2_zfmisc_1(A_98,A_98)))
      | ~ v3_funct_2(B_99,A_98,A_98)
      | ~ v1_funct_2(B_99,A_98,A_98)
      | ~ v1_funct_1(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_321,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_315])).

tff(c_325,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_321])).

tff(c_337,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_325])).

tff(c_479,plain,(
    ! [A_113,C_114,D_112,F_115,E_117,B_116] :
      ( k1_partfun1(A_113,B_116,C_114,D_112,E_117,F_115) = k5_relat_1(E_117,F_115)
      | ~ m1_subset_1(F_115,k1_zfmisc_1(k2_zfmisc_1(C_114,D_112)))
      | ~ v1_funct_1(F_115)
      | ~ m1_subset_1(E_117,k1_zfmisc_1(k2_zfmisc_1(A_113,B_116)))
      | ~ v1_funct_1(E_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1694,plain,(
    ! [E_155,A_159,B_156,A_157,B_158] :
      ( k1_partfun1(A_157,B_158,A_159,A_159,E_155,k2_funct_2(A_159,B_156)) = k5_relat_1(E_155,k2_funct_2(A_159,B_156))
      | ~ v1_funct_1(k2_funct_2(A_159,B_156))
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158)))
      | ~ v1_funct_1(E_155)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(k2_zfmisc_1(A_159,A_159)))
      | ~ v3_funct_2(B_156,A_159,A_159)
      | ~ v1_funct_2(B_156,A_159,A_159)
      | ~ v1_funct_1(B_156) ) ),
    inference(resolution,[status(thm)],[c_32,c_479])).

tff(c_1710,plain,(
    ! [A_159,B_156] :
      ( k1_partfun1('#skF_1','#skF_1',A_159,A_159,'#skF_2',k2_funct_2(A_159,B_156)) = k5_relat_1('#skF_2',k2_funct_2(A_159,B_156))
      | ~ v1_funct_1(k2_funct_2(A_159,B_156))
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(B_156,k1_zfmisc_1(k2_zfmisc_1(A_159,A_159)))
      | ~ v3_funct_2(B_156,A_159,A_159)
      | ~ v1_funct_2(B_156,A_159,A_159)
      | ~ v1_funct_1(B_156) ) ),
    inference(resolution,[status(thm)],[c_50,c_1694])).

tff(c_1731,plain,(
    ! [A_160,B_161] :
      ( k1_partfun1('#skF_1','#skF_1',A_160,A_160,'#skF_2',k2_funct_2(A_160,B_161)) = k5_relat_1('#skF_2',k2_funct_2(A_160,B_161))
      | ~ v1_funct_1(k2_funct_2(A_160,B_161))
      | ~ m1_subset_1(B_161,k1_zfmisc_1(k2_zfmisc_1(A_160,A_160)))
      | ~ v3_funct_2(B_161,A_160,A_160)
      | ~ v1_funct_2(B_161,A_160,A_160)
      | ~ v1_funct_1(B_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1710])).

tff(c_1747,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')) = k5_relat_1('#skF_2',k2_funct_2('#skF_1','#skF_2'))
    | ~ v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_1731])).

tff(c_1767,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')) = k5_relat_1('#skF_2',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_337,c_336,c_336,c_336,c_1747])).

tff(c_48,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1'))
    | ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_84,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_2('#skF_1','#skF_2')),k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_338,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_84])).

tff(c_1772,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_2',k2_funct_1('#skF_2')),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1767,c_338])).

tff(c_1779,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k1_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1772])).

tff(c_1782,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_56,c_266,c_202,c_291,c_1779])).

tff(c_1783,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2047,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2035,c_1783])).

tff(c_2593,plain,(
    ~ r2_relset_1('#skF_1','#skF_1',k5_relat_1(k2_funct_1('#skF_2'),'#skF_2'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2457,c_2047])).

tff(c_2604,plain,
    ( ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1(k2_relat_1('#skF_2')),k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_2593])).

tff(c_2607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_56,c_1958,c_1812,c_1895,c_2604])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:55:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.06/1.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.06/1.95  
% 5.06/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.06/1.95  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.06/1.95  
% 5.06/1.95  %Foreground sorts:
% 5.06/1.95  
% 5.06/1.95  
% 5.06/1.95  %Background operators:
% 5.06/1.95  
% 5.06/1.95  
% 5.06/1.95  %Foreground operators:
% 5.06/1.95  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.06/1.95  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.06/1.95  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.06/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.06/1.95  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.06/1.95  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.06/1.95  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.06/1.95  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.06/1.95  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.06/1.95  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.06/1.95  tff('#skF_2', type, '#skF_2': $i).
% 5.06/1.95  tff('#skF_1', type, '#skF_1': $i).
% 5.06/1.95  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.06/1.95  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.06/1.95  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.06/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.06/1.95  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.06/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.06/1.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.06/1.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.06/1.95  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.06/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.06/1.95  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.06/1.95  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.06/1.95  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.06/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.06/1.95  
% 5.06/1.97  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.06/1.97  tff(f_143, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 5.06/1.97  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.06/1.97  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.06/1.97  tff(f_122, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.06/1.97  tff(f_64, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 5.06/1.97  tff(f_62, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.06/1.97  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.06/1.97  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.06/1.97  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.06/1.97  tff(f_120, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.06/1.97  tff(f_100, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 5.06/1.97  tff(f_110, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.06/1.97  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.06/1.97  tff(f_130, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 5.06/1.97  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.06/1.97  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.06/1.97  tff(c_71, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.06/1.97  tff(c_77, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_50, c_71])).
% 5.06/1.97  tff(c_83, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_77])).
% 5.06/1.97  tff(c_56, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.06/1.97  tff(c_52, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.06/1.97  tff(c_1948, plain, (![C_199, A_200, B_201]: (v2_funct_1(C_199) | ~v3_funct_2(C_199, A_200, B_201) | ~v1_funct_1(C_199) | ~m1_subset_1(C_199, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.06/1.97  tff(c_1954, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1948])).
% 5.06/1.97  tff(c_1958, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_1954])).
% 5.06/1.97  tff(c_44, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.06/1.97  tff(c_20, plain, (![A_17]: (m1_subset_1(k6_relat_1(A_17), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.06/1.97  tff(c_57, plain, (![A_17]: (m1_subset_1(k6_partfun1(A_17), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_20])).
% 5.06/1.97  tff(c_1807, plain, (![A_172, B_173, D_174]: (r2_relset_1(A_172, B_173, D_174, D_174) | ~m1_subset_1(D_174, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.06/1.97  tff(c_1812, plain, (![A_17]: (r2_relset_1(A_17, A_17, k6_partfun1(A_17), k6_partfun1(A_17)))), inference(resolution, [status(thm)], [c_57, c_1807])).
% 5.06/1.97  tff(c_1786, plain, (![C_163, B_164, A_165]: (v5_relat_1(C_163, B_164) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_165, B_164))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.06/1.97  tff(c_1794, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_1786])).
% 5.06/1.97  tff(c_1815, plain, (![B_176, A_177]: (k2_relat_1(B_176)=A_177 | ~v2_funct_2(B_176, A_177) | ~v5_relat_1(B_176, A_177) | ~v1_relat_1(B_176))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.06/1.97  tff(c_1821, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1794, c_1815])).
% 5.06/1.97  tff(c_1827, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_1821])).
% 5.06/1.97  tff(c_1828, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_1827])).
% 5.06/1.97  tff(c_1882, plain, (![C_189, B_190, A_191]: (v2_funct_2(C_189, B_190) | ~v3_funct_2(C_189, A_191, B_190) | ~v1_funct_1(C_189) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_191, B_190))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.06/1.97  tff(c_1888, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1882])).
% 5.06/1.97  tff(c_1892, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_1888])).
% 5.06/1.97  tff(c_1894, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1828, c_1892])).
% 5.06/1.97  tff(c_1895, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1827])).
% 5.06/1.97  tff(c_6, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_relat_1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.06/1.97  tff(c_59, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_partfun1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6])).
% 5.06/1.97  tff(c_54, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.06/1.97  tff(c_2025, plain, (![A_217, B_218]: (k2_funct_2(A_217, B_218)=k2_funct_1(B_218) | ~m1_subset_1(B_218, k1_zfmisc_1(k2_zfmisc_1(A_217, A_217))) | ~v3_funct_2(B_218, A_217, A_217) | ~v1_funct_2(B_218, A_217, A_217) | ~v1_funct_1(B_218))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.06/1.97  tff(c_2031, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_2025])).
% 5.06/1.97  tff(c_2035, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2031])).
% 5.06/1.97  tff(c_2013, plain, (![A_214, B_215]: (v1_funct_1(k2_funct_2(A_214, B_215)) | ~m1_subset_1(B_215, k1_zfmisc_1(k2_zfmisc_1(A_214, A_214))) | ~v3_funct_2(B_215, A_214, A_214) | ~v1_funct_2(B_215, A_214, A_214) | ~v1_funct_1(B_215))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.06/1.97  tff(c_2019, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_2013])).
% 5.06/1.97  tff(c_2023, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2019])).
% 5.06/1.97  tff(c_2045, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2035, c_2023])).
% 5.06/1.97  tff(c_32, plain, (![A_23, B_24]: (m1_subset_1(k2_funct_2(A_23, B_24), k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))) | ~m1_subset_1(B_24, k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))) | ~v3_funct_2(B_24, A_23, A_23) | ~v1_funct_2(B_24, A_23, A_23) | ~v1_funct_1(B_24))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.06/1.97  tff(c_2190, plain, (![D_227, A_228, C_229, E_232, B_231, F_230]: (k1_partfun1(A_228, B_231, C_229, D_227, E_232, F_230)=k5_relat_1(E_232, F_230) | ~m1_subset_1(F_230, k1_zfmisc_1(k2_zfmisc_1(C_229, D_227))) | ~v1_funct_1(F_230) | ~m1_subset_1(E_232, k1_zfmisc_1(k2_zfmisc_1(A_228, B_231))) | ~v1_funct_1(E_232))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.06/1.97  tff(c_2198, plain, (![A_228, B_231, E_232]: (k1_partfun1(A_228, B_231, '#skF_1', '#skF_1', E_232, '#skF_2')=k5_relat_1(E_232, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_232, k1_zfmisc_1(k2_zfmisc_1(A_228, B_231))) | ~v1_funct_1(E_232))), inference(resolution, [status(thm)], [c_50, c_2190])).
% 5.06/1.97  tff(c_2217, plain, (![A_233, B_234, E_235]: (k1_partfun1(A_233, B_234, '#skF_1', '#skF_1', E_235, '#skF_2')=k5_relat_1(E_235, '#skF_2') | ~m1_subset_1(E_235, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))) | ~v1_funct_1(E_235))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2198])).
% 5.06/1.97  tff(c_2436, plain, (![A_242, B_243]: (k1_partfun1(A_242, A_242, '#skF_1', '#skF_1', k2_funct_2(A_242, B_243), '#skF_2')=k5_relat_1(k2_funct_2(A_242, B_243), '#skF_2') | ~v1_funct_1(k2_funct_2(A_242, B_243)) | ~m1_subset_1(B_243, k1_zfmisc_1(k2_zfmisc_1(A_242, A_242))) | ~v3_funct_2(B_243, A_242, A_242) | ~v1_funct_2(B_243, A_242, A_242) | ~v1_funct_1(B_243))), inference(resolution, [status(thm)], [c_32, c_2217])).
% 5.06/1.97  tff(c_2446, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2')=k5_relat_1(k2_funct_2('#skF_1', '#skF_2'), '#skF_2') | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_2436])).
% 5.06/1.97  tff(c_2457, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2')=k5_relat_1(k2_funct_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_2045, c_2035, c_2035, c_2035, c_2446])).
% 5.06/1.97  tff(c_256, plain, (![C_83, A_84, B_85]: (v2_funct_1(C_83) | ~v3_funct_2(C_83, A_84, B_85) | ~v1_funct_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.06/1.97  tff(c_262, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_256])).
% 5.06/1.97  tff(c_266, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_262])).
% 5.06/1.97  tff(c_197, plain, (![A_72, B_73, D_74]: (r2_relset_1(A_72, B_73, D_74, D_74) | ~m1_subset_1(D_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.06/1.97  tff(c_202, plain, (![A_17]: (r2_relset_1(A_17, A_17, k6_partfun1(A_17), k6_partfun1(A_17)))), inference(resolution, [status(thm)], [c_57, c_197])).
% 5.06/1.97  tff(c_216, plain, (![A_77, B_78, C_79]: (k1_relset_1(A_77, B_78, C_79)=k1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.06/1.97  tff(c_224, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_216])).
% 5.06/1.97  tff(c_280, plain, (![A_91, B_92]: (k1_relset_1(A_91, A_91, B_92)=A_91 | ~m1_subset_1(B_92, k1_zfmisc_1(k2_zfmisc_1(A_91, A_91))) | ~v1_funct_2(B_92, A_91, A_91) | ~v1_funct_1(B_92))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.06/1.97  tff(c_286, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_280])).
% 5.06/1.97  tff(c_291, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_224, c_286])).
% 5.06/1.97  tff(c_8, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_relat_1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.06/1.97  tff(c_58, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_partfun1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_8])).
% 5.06/1.97  tff(c_326, plain, (![A_100, B_101]: (k2_funct_2(A_100, B_101)=k2_funct_1(B_101) | ~m1_subset_1(B_101, k1_zfmisc_1(k2_zfmisc_1(A_100, A_100))) | ~v3_funct_2(B_101, A_100, A_100) | ~v1_funct_2(B_101, A_100, A_100) | ~v1_funct_1(B_101))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.06/1.97  tff(c_332, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_326])).
% 5.06/1.97  tff(c_336, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_332])).
% 5.06/1.97  tff(c_315, plain, (![A_98, B_99]: (v1_funct_1(k2_funct_2(A_98, B_99)) | ~m1_subset_1(B_99, k1_zfmisc_1(k2_zfmisc_1(A_98, A_98))) | ~v3_funct_2(B_99, A_98, A_98) | ~v1_funct_2(B_99, A_98, A_98) | ~v1_funct_1(B_99))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.06/1.97  tff(c_321, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_315])).
% 5.06/1.97  tff(c_325, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_321])).
% 5.06/1.97  tff(c_337, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_336, c_325])).
% 5.06/1.97  tff(c_479, plain, (![A_113, C_114, D_112, F_115, E_117, B_116]: (k1_partfun1(A_113, B_116, C_114, D_112, E_117, F_115)=k5_relat_1(E_117, F_115) | ~m1_subset_1(F_115, k1_zfmisc_1(k2_zfmisc_1(C_114, D_112))) | ~v1_funct_1(F_115) | ~m1_subset_1(E_117, k1_zfmisc_1(k2_zfmisc_1(A_113, B_116))) | ~v1_funct_1(E_117))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.06/1.97  tff(c_1694, plain, (![E_155, A_159, B_156, A_157, B_158]: (k1_partfun1(A_157, B_158, A_159, A_159, E_155, k2_funct_2(A_159, B_156))=k5_relat_1(E_155, k2_funct_2(A_159, B_156)) | ~v1_funct_1(k2_funct_2(A_159, B_156)) | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))) | ~v1_funct_1(E_155) | ~m1_subset_1(B_156, k1_zfmisc_1(k2_zfmisc_1(A_159, A_159))) | ~v3_funct_2(B_156, A_159, A_159) | ~v1_funct_2(B_156, A_159, A_159) | ~v1_funct_1(B_156))), inference(resolution, [status(thm)], [c_32, c_479])).
% 5.06/1.97  tff(c_1710, plain, (![A_159, B_156]: (k1_partfun1('#skF_1', '#skF_1', A_159, A_159, '#skF_2', k2_funct_2(A_159, B_156))=k5_relat_1('#skF_2', k2_funct_2(A_159, B_156)) | ~v1_funct_1(k2_funct_2(A_159, B_156)) | ~v1_funct_1('#skF_2') | ~m1_subset_1(B_156, k1_zfmisc_1(k2_zfmisc_1(A_159, A_159))) | ~v3_funct_2(B_156, A_159, A_159) | ~v1_funct_2(B_156, A_159, A_159) | ~v1_funct_1(B_156))), inference(resolution, [status(thm)], [c_50, c_1694])).
% 5.06/1.97  tff(c_1731, plain, (![A_160, B_161]: (k1_partfun1('#skF_1', '#skF_1', A_160, A_160, '#skF_2', k2_funct_2(A_160, B_161))=k5_relat_1('#skF_2', k2_funct_2(A_160, B_161)) | ~v1_funct_1(k2_funct_2(A_160, B_161)) | ~m1_subset_1(B_161, k1_zfmisc_1(k2_zfmisc_1(A_160, A_160))) | ~v3_funct_2(B_161, A_160, A_160) | ~v1_funct_2(B_161, A_160, A_160) | ~v1_funct_1(B_161))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1710])).
% 5.06/1.97  tff(c_1747, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2'))=k5_relat_1('#skF_2', k2_funct_2('#skF_1', '#skF_2')) | ~v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_1731])).
% 5.06/1.97  tff(c_1767, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2'))=k5_relat_1('#skF_2', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_337, c_336, c_336, c_336, c_1747])).
% 5.06/1.97  tff(c_48, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1')) | ~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.06/1.97  tff(c_84, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_2('#skF_1', '#skF_2')), k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_48])).
% 5.06/1.97  tff(c_338, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_336, c_84])).
% 5.06/1.97  tff(c_1772, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_2', k2_funct_1('#skF_2')), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1767, c_338])).
% 5.06/1.97  tff(c_1779, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k1_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_58, c_1772])).
% 5.06/1.97  tff(c_1782, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_56, c_266, c_202, c_291, c_1779])).
% 5.06/1.97  tff(c_1783, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_48])).
% 5.06/1.97  tff(c_2047, plain, (~r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2035, c_1783])).
% 5.06/1.97  tff(c_2593, plain, (~r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k2_funct_1('#skF_2'), '#skF_2'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2457, c_2047])).
% 5.06/1.97  tff(c_2604, plain, (~r2_relset_1('#skF_1', '#skF_1', k6_partfun1(k2_relat_1('#skF_2')), k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_59, c_2593])).
% 5.06/1.97  tff(c_2607, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_56, c_1958, c_1812, c_1895, c_2604])).
% 5.06/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.06/1.97  
% 5.06/1.97  Inference rules
% 5.06/1.97  ----------------------
% 5.06/1.97  #Ref     : 0
% 5.06/1.97  #Sup     : 547
% 5.06/1.97  #Fact    : 0
% 5.06/1.97  #Define  : 0
% 5.06/1.97  #Split   : 4
% 5.06/1.97  #Chain   : 0
% 5.06/1.97  #Close   : 0
% 5.06/1.97  
% 5.06/1.97  Ordering : KBO
% 5.06/1.97  
% 5.06/1.97  Simplification rules
% 5.06/1.97  ----------------------
% 5.06/1.97  #Subsume      : 1
% 5.06/1.97  #Demod        : 1276
% 5.06/1.97  #Tautology    : 227
% 5.06/1.97  #SimpNegUnit  : 2
% 5.06/1.97  #BackRed      : 49
% 5.06/1.97  
% 5.06/1.97  #Partial instantiations: 0
% 5.06/1.97  #Strategies tried      : 1
% 5.06/1.97  
% 5.06/1.97  Timing (in seconds)
% 5.06/1.97  ----------------------
% 5.06/1.98  Preprocessing        : 0.34
% 5.06/1.98  Parsing              : 0.18
% 5.06/1.98  CNF conversion       : 0.02
% 5.06/1.98  Main loop            : 0.84
% 5.06/1.98  Inferencing          : 0.28
% 5.06/1.98  Reduction            : 0.32
% 5.06/1.98  Demodulation         : 0.24
% 5.06/1.98  BG Simplification    : 0.03
% 5.06/1.98  Subsumption          : 0.15
% 5.06/1.98  Abstraction          : 0.04
% 5.06/1.98  MUC search           : 0.00
% 5.06/1.98  Cooper               : 0.00
% 5.06/1.98  Total                : 1.23
% 5.06/1.98  Index Insertion      : 0.00
% 5.06/1.98  Index Deletion       : 0.00
% 5.06/1.98  Index Matching       : 0.00
% 5.06/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
