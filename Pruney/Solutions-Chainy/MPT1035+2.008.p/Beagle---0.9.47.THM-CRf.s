%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:59 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :  157 (1010 expanded)
%              Number of leaves         :   32 ( 332 expanded)
%              Depth                    :   15
%              Number of atoms          :  323 (3661 expanded)
%              Number of equality atoms :   82 (1242 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ( B = k1_xboole_0
               => A = k1_xboole_0 )
             => ( r1_partfun1(C,D)
              <=> ! [E] :
                    ( r2_hidden(E,k1_relset_1(A,B,C))
                   => k1_funct_1(C,E) = k1_funct_1(D,E) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_68,axiom,(
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

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
           => ( r1_partfun1(A,B)
            <=> ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_partfun1)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_61,plain,(
    ! [B_39,A_40] :
      ( v1_relat_1(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40))
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_67,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_61])).

tff(c_73,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_67])).

tff(c_288,plain,(
    ! [C_84,A_85,B_86] :
      ( v4_relat_1(C_84,A_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_296,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_288])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_48,plain,
    ( k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6')
    | ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_74,plain,(
    ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_64,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_61])).

tff(c_70,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_64])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_84,plain,(
    ! [C_44,A_45,B_46] :
      ( v4_relat_1(C_44,A_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_92,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_84])).

tff(c_36,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_59,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_40,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_101,plain,(
    ! [A_52,B_53,C_54] :
      ( k1_relset_1(A_52,B_53,C_54) = k1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_108,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_101])).

tff(c_125,plain,(
    ! [B_63,A_64,C_65] :
      ( k1_xboole_0 = B_63
      | k1_relset_1(A_64,B_63,C_65) = A_64
      | ~ v1_funct_2(C_65,A_64,B_63)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_64,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_128,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_125])).

tff(c_134,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_108,c_128])).

tff(c_135,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_134])).

tff(c_185,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_1'(A_73,B_74),k1_relat_1(A_73))
      | r1_partfun1(A_73,B_74)
      | ~ r1_tarski(k1_relat_1(A_73),k1_relat_1(B_74))
      | ~ v1_funct_1(B_74)
      | ~ v1_relat_1(B_74)
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_109,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_101])).

tff(c_58,plain,(
    ! [E_36] :
      ( r1_partfun1('#skF_4','#skF_5')
      | k1_funct_1('#skF_5',E_36) = k1_funct_1('#skF_4',E_36)
      | ~ r2_hidden(E_36,k1_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_93,plain,(
    ! [E_36] :
      ( k1_funct_1('#skF_5',E_36) = k1_funct_1('#skF_4',E_36)
      | ~ r2_hidden(E_36,k1_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_58])).

tff(c_115,plain,(
    ! [E_36] :
      ( k1_funct_1('#skF_5',E_36) = k1_funct_1('#skF_4',E_36)
      | ~ r2_hidden(E_36,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_93])).

tff(c_189,plain,(
    ! [B_74] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_74)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_74))
      | r1_partfun1('#skF_4',B_74)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_74))
      | ~ v1_funct_1(B_74)
      | ~ v1_relat_1(B_74)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_185,c_115])).

tff(c_233,plain,(
    ! [B_80] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_80)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_80))
      | r1_partfun1('#skF_4',B_80)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_80))
      | ~ v1_funct_1(B_80)
      | ~ v1_relat_1(B_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_46,c_189])).

tff(c_236,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_233])).

tff(c_241,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_42,c_236])).

tff(c_242,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_241])).

tff(c_246,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_249,plain,
    ( ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_246])).

tff(c_253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_92,c_249])).

tff(c_255,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_254,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_30,plain,(
    ! [B_23,A_17] :
      ( k1_funct_1(B_23,'#skF_1'(A_17,B_23)) != k1_funct_1(A_17,'#skF_1'(A_17,B_23))
      | r1_partfun1(A_17,B_23)
      | ~ r1_tarski(k1_relat_1(A_17),k1_relat_1(B_23))
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_272,plain,
    ( r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_30])).

tff(c_277,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_46,c_70,c_42,c_255,c_135,c_272])).

tff(c_279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_277])).

tff(c_280,plain,(
    k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_281,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_313,plain,(
    ! [A_94,B_95,C_96] :
      ( k1_relset_1(A_94,B_95,C_96) = k1_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_320,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_313])).

tff(c_336,plain,(
    ! [B_104,A_105,C_106] :
      ( k1_xboole_0 = B_104
      | k1_relset_1(A_105,B_104,C_106) = A_105
      | ~ v1_funct_2(C_106,A_105,B_104)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_105,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_339,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_336])).

tff(c_345,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_320,c_339])).

tff(c_346,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_345])).

tff(c_321,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_313])).

tff(c_50,plain,
    ( r2_hidden('#skF_6',k1_relset_1('#skF_2','#skF_3','#skF_4'))
    | ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_282,plain,(
    ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_282])).

tff(c_285,plain,(
    r2_hidden('#skF_6',k1_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_326,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_285])).

tff(c_407,plain,(
    ! [B_119,C_120,A_121] :
      ( k1_funct_1(B_119,C_120) = k1_funct_1(A_121,C_120)
      | ~ r2_hidden(C_120,k1_relat_1(A_121))
      | ~ r1_partfun1(A_121,B_119)
      | ~ r1_tarski(k1_relat_1(A_121),k1_relat_1(B_119))
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119)
      | ~ v1_funct_1(A_121)
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_413,plain,(
    ! [B_119] :
      ( k1_funct_1(B_119,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_119)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_119))
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_326,c_407])).

tff(c_450,plain,(
    ! [B_124] :
      ( k1_funct_1(B_124,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_124)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_124))
      | ~ v1_funct_1(B_124)
      | ~ v1_relat_1(B_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_46,c_413])).

tff(c_453,plain,
    ( k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_450])).

tff(c_458,plain,
    ( k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_42,c_281,c_453])).

tff(c_459,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_280,c_458])).

tff(c_478,plain,
    ( ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_459])).

tff(c_482,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_296,c_478])).

tff(c_484,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_483,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_489,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_483])).

tff(c_501,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_44])).

tff(c_502,plain,(
    ! [B_130,A_131] :
      ( v1_relat_1(B_130)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(A_131))
      | ~ v1_relat_1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_508,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_501,c_502])).

tff(c_514,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_508])).

tff(c_754,plain,(
    ! [C_175,A_176,B_177] :
      ( v4_relat_1(C_175,A_176)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_762,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_501,c_754])).

tff(c_515,plain,(
    ~ r1_partfun1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_494,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_38])).

tff(c_505,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_494,c_502])).

tff(c_511,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_505])).

tff(c_518,plain,(
    ! [C_132,A_133,B_134] :
      ( v4_relat_1(C_132,A_133)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_526,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_501,c_518])).

tff(c_495,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_40])).

tff(c_545,plain,(
    ! [A_143,B_144,C_145] :
      ( k1_relset_1(A_143,B_144,C_145) = k1_relat_1(C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_552,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_494,c_545])).

tff(c_24,plain,(
    ! [B_15,C_16] :
      ( k1_relset_1(k1_xboole_0,B_15,C_16) = k1_xboole_0
      | ~ v1_funct_2(C_16,k1_xboole_0,B_15)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_581,plain,(
    ! [B_150,C_151] :
      ( k1_relset_1('#skF_3',B_150,C_151) = '#skF_3'
      | ~ v1_funct_2(C_151,'#skF_3',B_150)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_150))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_484,c_484,c_484,c_24])).

tff(c_584,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_494,c_581])).

tff(c_590,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_552,c_584])).

tff(c_683,plain,(
    ! [A_164,B_165] :
      ( r2_hidden('#skF_1'(A_164,B_165),k1_relat_1(A_164))
      | r1_partfun1(A_164,B_165)
      | ~ r1_tarski(k1_relat_1(A_164),k1_relat_1(B_165))
      | ~ v1_funct_1(B_165)
      | ~ v1_relat_1(B_165)
      | ~ v1_funct_1(A_164)
      | ~ v1_relat_1(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_553,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_501,c_545])).

tff(c_542,plain,(
    ! [E_36] :
      ( r1_partfun1('#skF_4','#skF_5')
      | k1_funct_1('#skF_5',E_36) = k1_funct_1('#skF_4',E_36)
      | ~ r2_hidden(E_36,k1_relset_1('#skF_3','#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_58])).

tff(c_543,plain,(
    ! [E_36] :
      ( k1_funct_1('#skF_5',E_36) = k1_funct_1('#skF_4',E_36)
      | ~ r2_hidden(E_36,k1_relset_1('#skF_3','#skF_3','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_515,c_542])).

tff(c_558,plain,(
    ! [E_36] :
      ( k1_funct_1('#skF_5',E_36) = k1_funct_1('#skF_4',E_36)
      | ~ r2_hidden(E_36,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_553,c_543])).

tff(c_687,plain,(
    ! [B_165] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_165)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_165))
      | r1_partfun1('#skF_4',B_165)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_165))
      | ~ v1_funct_1(B_165)
      | ~ v1_relat_1(B_165)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_683,c_558])).

tff(c_697,plain,(
    ! [B_167] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_167)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_167))
      | r1_partfun1('#skF_4',B_167)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_167))
      | ~ v1_funct_1(B_167)
      | ~ v1_relat_1(B_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_46,c_687])).

tff(c_700,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_590,c_697])).

tff(c_705,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_42,c_700])).

tff(c_706,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5'))
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_515,c_705])).

tff(c_714,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_706])).

tff(c_717,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_714])).

tff(c_721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_526,c_717])).

tff(c_723,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_706])).

tff(c_722,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_4','#skF_5')) = k1_funct_1('#skF_4','#skF_1'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_706])).

tff(c_732,plain,
    ( r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_722,c_30])).

tff(c_737,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_46,c_511,c_42,c_723,c_590,c_732])).

tff(c_739,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_515,c_737])).

tff(c_740,plain,(
    k1_funct_1('#skF_5','#skF_6') != k1_funct_1('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_741,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_769,plain,(
    ! [A_180,B_181,C_182] :
      ( k1_relset_1(A_180,B_181,C_182) = k1_relat_1(C_182)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_776,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_494,c_769])).

tff(c_818,plain,(
    ! [B_188,C_189] :
      ( k1_relset_1('#skF_3',B_188,C_189) = '#skF_3'
      | ~ v1_funct_2(C_189,'#skF_3',B_188)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_188))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_484,c_484,c_484,c_484,c_24])).

tff(c_821,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_494,c_818])).

tff(c_827,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_776,c_821])).

tff(c_777,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_501,c_769])).

tff(c_753,plain,(
    r2_hidden('#skF_6',k1_relset_1('#skF_3','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_741,c_489,c_50])).

tff(c_782,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_777,c_753])).

tff(c_911,plain,(
    ! [B_203,C_204,A_205] :
      ( k1_funct_1(B_203,C_204) = k1_funct_1(A_205,C_204)
      | ~ r2_hidden(C_204,k1_relat_1(A_205))
      | ~ r1_partfun1(A_205,B_203)
      | ~ r1_tarski(k1_relat_1(A_205),k1_relat_1(B_203))
      | ~ v1_funct_1(B_203)
      | ~ v1_relat_1(B_203)
      | ~ v1_funct_1(A_205)
      | ~ v1_relat_1(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_917,plain,(
    ! [B_203] :
      ( k1_funct_1(B_203,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_203)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_203))
      | ~ v1_funct_1(B_203)
      | ~ v1_relat_1(B_203)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_782,c_911])).

tff(c_924,plain,(
    ! [B_206] :
      ( k1_funct_1(B_206,'#skF_6') = k1_funct_1('#skF_4','#skF_6')
      | ~ r1_partfun1('#skF_4',B_206)
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1(B_206))
      | ~ v1_funct_1(B_206)
      | ~ v1_relat_1(B_206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_46,c_917])).

tff(c_927,plain,
    ( k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ r1_partfun1('#skF_4','#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_827,c_924])).

tff(c_932,plain,
    ( k1_funct_1('#skF_5','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_42,c_741,c_927])).

tff(c_933,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_740,c_932])).

tff(c_939,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_933])).

tff(c_943,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_762,c_939])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:56:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.53  
% 3.37/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.53  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.37/1.53  
% 3.37/1.53  %Foreground sorts:
% 3.37/1.53  
% 3.37/1.53  
% 3.37/1.53  %Background operators:
% 3.37/1.53  
% 3.37/1.53  
% 3.37/1.53  %Foreground operators:
% 3.37/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.37/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.37/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.37/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.37/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.37/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.37/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.37/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.37/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.37/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.37/1.53  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.37/1.53  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.37/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.37/1.53  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.37/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.37/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.37/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.37/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.37/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.37/1.53  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.37/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.37/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.37/1.53  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 3.37/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.37/1.53  
% 3.37/1.55  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.37/1.55  tff(f_117, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (r1_partfun1(C, D) <=> (![E]: (r2_hidden(E, k1_relset_1(A, B, C)) => (k1_funct_1(C, E) = k1_funct_1(D, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_2)).
% 3.37/1.55  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.37/1.55  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.37/1.55  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.37/1.55  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.37/1.55  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.37/1.55  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) => (r1_partfun1(A, B) <=> (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_partfun1)).
% 3.37/1.55  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.37/1.55  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.37/1.55  tff(c_61, plain, (![B_39, A_40]: (v1_relat_1(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.37/1.55  tff(c_67, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_61])).
% 3.37/1.55  tff(c_73, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_67])).
% 3.37/1.55  tff(c_288, plain, (![C_84, A_85, B_86]: (v4_relat_1(C_84, A_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.37/1.55  tff(c_296, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_288])).
% 3.37/1.55  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.37/1.55  tff(c_48, plain, (k1_funct_1('#skF_5', '#skF_6')!=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.37/1.55  tff(c_74, plain, (~r1_partfun1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_48])).
% 3.37/1.55  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.37/1.55  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.37/1.55  tff(c_64, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_61])).
% 3.37/1.55  tff(c_70, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_64])).
% 3.37/1.55  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.37/1.55  tff(c_84, plain, (![C_44, A_45, B_46]: (v4_relat_1(C_44, A_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.37/1.55  tff(c_92, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_84])).
% 3.37/1.55  tff(c_36, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.37/1.55  tff(c_59, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_36])).
% 3.37/1.55  tff(c_40, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.37/1.55  tff(c_101, plain, (![A_52, B_53, C_54]: (k1_relset_1(A_52, B_53, C_54)=k1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.37/1.55  tff(c_108, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_101])).
% 3.37/1.55  tff(c_125, plain, (![B_63, A_64, C_65]: (k1_xboole_0=B_63 | k1_relset_1(A_64, B_63, C_65)=A_64 | ~v1_funct_2(C_65, A_64, B_63) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_64, B_63))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.37/1.55  tff(c_128, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_125])).
% 3.37/1.55  tff(c_134, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_108, c_128])).
% 3.37/1.55  tff(c_135, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_59, c_134])).
% 3.37/1.55  tff(c_185, plain, (![A_73, B_74]: (r2_hidden('#skF_1'(A_73, B_74), k1_relat_1(A_73)) | r1_partfun1(A_73, B_74) | ~r1_tarski(k1_relat_1(A_73), k1_relat_1(B_74)) | ~v1_funct_1(B_74) | ~v1_relat_1(B_74) | ~v1_funct_1(A_73) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.37/1.55  tff(c_109, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_101])).
% 3.37/1.55  tff(c_58, plain, (![E_36]: (r1_partfun1('#skF_4', '#skF_5') | k1_funct_1('#skF_5', E_36)=k1_funct_1('#skF_4', E_36) | ~r2_hidden(E_36, k1_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.37/1.55  tff(c_93, plain, (![E_36]: (k1_funct_1('#skF_5', E_36)=k1_funct_1('#skF_4', E_36) | ~r2_hidden(E_36, k1_relset_1('#skF_2', '#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_74, c_58])).
% 3.37/1.55  tff(c_115, plain, (![E_36]: (k1_funct_1('#skF_5', E_36)=k1_funct_1('#skF_4', E_36) | ~r2_hidden(E_36, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_93])).
% 3.37/1.55  tff(c_189, plain, (![B_74]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_74))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_74)) | r1_partfun1('#skF_4', B_74) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_74)) | ~v1_funct_1(B_74) | ~v1_relat_1(B_74) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_185, c_115])).
% 3.37/1.55  tff(c_233, plain, (![B_80]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_80))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_80)) | r1_partfun1('#skF_4', B_80) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_80)) | ~v1_funct_1(B_80) | ~v1_relat_1(B_80))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_46, c_189])).
% 3.37/1.55  tff(c_236, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_135, c_233])).
% 3.37/1.55  tff(c_241, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_42, c_236])).
% 3.37/1.55  tff(c_242, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_74, c_241])).
% 3.37/1.55  tff(c_246, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_242])).
% 3.37/1.55  tff(c_249, plain, (~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_246])).
% 3.37/1.55  tff(c_253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_92, c_249])).
% 3.37/1.55  tff(c_255, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_242])).
% 3.37/1.55  tff(c_254, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_242])).
% 3.37/1.55  tff(c_30, plain, (![B_23, A_17]: (k1_funct_1(B_23, '#skF_1'(A_17, B_23))!=k1_funct_1(A_17, '#skF_1'(A_17, B_23)) | r1_partfun1(A_17, B_23) | ~r1_tarski(k1_relat_1(A_17), k1_relat_1(B_23)) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.37/1.55  tff(c_272, plain, (r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_254, c_30])).
% 3.37/1.55  tff(c_277, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_46, c_70, c_42, c_255, c_135, c_272])).
% 3.37/1.55  tff(c_279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_277])).
% 3.37/1.55  tff(c_280, plain, (k1_funct_1('#skF_5', '#skF_6')!=k1_funct_1('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_48])).
% 3.37/1.55  tff(c_281, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_48])).
% 3.37/1.55  tff(c_313, plain, (![A_94, B_95, C_96]: (k1_relset_1(A_94, B_95, C_96)=k1_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.37/1.55  tff(c_320, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_313])).
% 3.37/1.55  tff(c_336, plain, (![B_104, A_105, C_106]: (k1_xboole_0=B_104 | k1_relset_1(A_105, B_104, C_106)=A_105 | ~v1_funct_2(C_106, A_105, B_104) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_105, B_104))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.37/1.55  tff(c_339, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_336])).
% 3.37/1.55  tff(c_345, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_320, c_339])).
% 3.37/1.55  tff(c_346, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_59, c_345])).
% 3.37/1.55  tff(c_321, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_313])).
% 3.37/1.55  tff(c_50, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.37/1.55  tff(c_282, plain, (~r1_partfun1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_50])).
% 3.37/1.55  tff(c_284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_281, c_282])).
% 3.37/1.55  tff(c_285, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_50])).
% 3.37/1.55  tff(c_326, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_321, c_285])).
% 3.37/1.55  tff(c_407, plain, (![B_119, C_120, A_121]: (k1_funct_1(B_119, C_120)=k1_funct_1(A_121, C_120) | ~r2_hidden(C_120, k1_relat_1(A_121)) | ~r1_partfun1(A_121, B_119) | ~r1_tarski(k1_relat_1(A_121), k1_relat_1(B_119)) | ~v1_funct_1(B_119) | ~v1_relat_1(B_119) | ~v1_funct_1(A_121) | ~v1_relat_1(A_121))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.37/1.55  tff(c_413, plain, (![B_119]: (k1_funct_1(B_119, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_119) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_119)) | ~v1_funct_1(B_119) | ~v1_relat_1(B_119) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_326, c_407])).
% 3.37/1.55  tff(c_450, plain, (![B_124]: (k1_funct_1(B_124, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_124) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_124)) | ~v1_funct_1(B_124) | ~v1_relat_1(B_124))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_46, c_413])).
% 3.37/1.55  tff(c_453, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_346, c_450])).
% 3.37/1.55  tff(c_458, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_42, c_281, c_453])).
% 3.37/1.55  tff(c_459, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_280, c_458])).
% 3.37/1.55  tff(c_478, plain, (~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_459])).
% 3.37/1.55  tff(c_482, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_296, c_478])).
% 3.37/1.55  tff(c_484, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_36])).
% 3.37/1.55  tff(c_483, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_36])).
% 3.37/1.55  tff(c_489, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_484, c_483])).
% 3.37/1.55  tff(c_501, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_489, c_44])).
% 3.37/1.55  tff(c_502, plain, (![B_130, A_131]: (v1_relat_1(B_130) | ~m1_subset_1(B_130, k1_zfmisc_1(A_131)) | ~v1_relat_1(A_131))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.37/1.55  tff(c_508, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_501, c_502])).
% 3.37/1.55  tff(c_514, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_508])).
% 3.37/1.55  tff(c_754, plain, (![C_175, A_176, B_177]: (v4_relat_1(C_175, A_176) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.37/1.55  tff(c_762, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_501, c_754])).
% 3.37/1.55  tff(c_515, plain, (~r1_partfun1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_48])).
% 3.37/1.55  tff(c_494, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_489, c_38])).
% 3.37/1.55  tff(c_505, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_494, c_502])).
% 3.37/1.55  tff(c_511, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_505])).
% 3.37/1.55  tff(c_518, plain, (![C_132, A_133, B_134]: (v4_relat_1(C_132, A_133) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.37/1.55  tff(c_526, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_501, c_518])).
% 3.37/1.55  tff(c_495, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_489, c_40])).
% 3.37/1.55  tff(c_545, plain, (![A_143, B_144, C_145]: (k1_relset_1(A_143, B_144, C_145)=k1_relat_1(C_145) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.37/1.55  tff(c_552, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_494, c_545])).
% 3.37/1.55  tff(c_24, plain, (![B_15, C_16]: (k1_relset_1(k1_xboole_0, B_15, C_16)=k1_xboole_0 | ~v1_funct_2(C_16, k1_xboole_0, B_15) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_15))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.37/1.55  tff(c_581, plain, (![B_150, C_151]: (k1_relset_1('#skF_3', B_150, C_151)='#skF_3' | ~v1_funct_2(C_151, '#skF_3', B_150) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_150))))), inference(demodulation, [status(thm), theory('equality')], [c_484, c_484, c_484, c_484, c_24])).
% 3.37/1.55  tff(c_584, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_494, c_581])).
% 3.37/1.55  tff(c_590, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_495, c_552, c_584])).
% 3.37/1.55  tff(c_683, plain, (![A_164, B_165]: (r2_hidden('#skF_1'(A_164, B_165), k1_relat_1(A_164)) | r1_partfun1(A_164, B_165) | ~r1_tarski(k1_relat_1(A_164), k1_relat_1(B_165)) | ~v1_funct_1(B_165) | ~v1_relat_1(B_165) | ~v1_funct_1(A_164) | ~v1_relat_1(A_164))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.37/1.55  tff(c_553, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_501, c_545])).
% 3.37/1.55  tff(c_542, plain, (![E_36]: (r1_partfun1('#skF_4', '#skF_5') | k1_funct_1('#skF_5', E_36)=k1_funct_1('#skF_4', E_36) | ~r2_hidden(E_36, k1_relset_1('#skF_3', '#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_489, c_58])).
% 3.37/1.55  tff(c_543, plain, (![E_36]: (k1_funct_1('#skF_5', E_36)=k1_funct_1('#skF_4', E_36) | ~r2_hidden(E_36, k1_relset_1('#skF_3', '#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_515, c_542])).
% 3.37/1.55  tff(c_558, plain, (![E_36]: (k1_funct_1('#skF_5', E_36)=k1_funct_1('#skF_4', E_36) | ~r2_hidden(E_36, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_553, c_543])).
% 3.37/1.55  tff(c_687, plain, (![B_165]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_165))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_165)) | r1_partfun1('#skF_4', B_165) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_165)) | ~v1_funct_1(B_165) | ~v1_relat_1(B_165) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_683, c_558])).
% 3.37/1.55  tff(c_697, plain, (![B_167]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_167))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_167)) | r1_partfun1('#skF_4', B_167) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_167)) | ~v1_funct_1(B_167) | ~v1_relat_1(B_167))), inference(demodulation, [status(thm), theory('equality')], [c_514, c_46, c_687])).
% 3.37/1.55  tff(c_700, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_590, c_697])).
% 3.37/1.55  tff(c_705, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_511, c_42, c_700])).
% 3.37/1.55  tff(c_706, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5')) | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_515, c_705])).
% 3.37/1.55  tff(c_714, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_706])).
% 3.37/1.55  tff(c_717, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_714])).
% 3.37/1.55  tff(c_721, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_514, c_526, c_717])).
% 3.37/1.55  tff(c_723, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_706])).
% 3.37/1.55  tff(c_722, plain, (k1_funct_1('#skF_5', '#skF_1'('#skF_4', '#skF_5'))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_706])).
% 3.37/1.55  tff(c_732, plain, (r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_722, c_30])).
% 3.37/1.55  tff(c_737, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_514, c_46, c_511, c_42, c_723, c_590, c_732])).
% 3.37/1.55  tff(c_739, plain, $false, inference(negUnitSimplification, [status(thm)], [c_515, c_737])).
% 3.37/1.55  tff(c_740, plain, (k1_funct_1('#skF_5', '#skF_6')!=k1_funct_1('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_48])).
% 3.37/1.55  tff(c_741, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_48])).
% 3.37/1.55  tff(c_769, plain, (![A_180, B_181, C_182]: (k1_relset_1(A_180, B_181, C_182)=k1_relat_1(C_182) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.37/1.55  tff(c_776, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_494, c_769])).
% 3.37/1.55  tff(c_818, plain, (![B_188, C_189]: (k1_relset_1('#skF_3', B_188, C_189)='#skF_3' | ~v1_funct_2(C_189, '#skF_3', B_188) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_188))))), inference(demodulation, [status(thm), theory('equality')], [c_484, c_484, c_484, c_484, c_24])).
% 3.37/1.55  tff(c_821, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_494, c_818])).
% 3.37/1.55  tff(c_827, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_495, c_776, c_821])).
% 3.37/1.55  tff(c_777, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_501, c_769])).
% 3.37/1.55  tff(c_753, plain, (r2_hidden('#skF_6', k1_relset_1('#skF_3', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_741, c_489, c_50])).
% 3.37/1.55  tff(c_782, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_777, c_753])).
% 3.37/1.55  tff(c_911, plain, (![B_203, C_204, A_205]: (k1_funct_1(B_203, C_204)=k1_funct_1(A_205, C_204) | ~r2_hidden(C_204, k1_relat_1(A_205)) | ~r1_partfun1(A_205, B_203) | ~r1_tarski(k1_relat_1(A_205), k1_relat_1(B_203)) | ~v1_funct_1(B_203) | ~v1_relat_1(B_203) | ~v1_funct_1(A_205) | ~v1_relat_1(A_205))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.37/1.55  tff(c_917, plain, (![B_203]: (k1_funct_1(B_203, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_203) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_203)) | ~v1_funct_1(B_203) | ~v1_relat_1(B_203) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_782, c_911])).
% 3.37/1.55  tff(c_924, plain, (![B_206]: (k1_funct_1(B_206, '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', B_206) | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1(B_206)) | ~v1_funct_1(B_206) | ~v1_relat_1(B_206))), inference(demodulation, [status(thm), theory('equality')], [c_514, c_46, c_917])).
% 3.37/1.55  tff(c_927, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_partfun1('#skF_4', '#skF_5') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_827, c_924])).
% 3.37/1.55  tff(c_932, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_511, c_42, c_741, c_927])).
% 3.37/1.55  tff(c_933, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_740, c_932])).
% 3.37/1.55  tff(c_939, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_933])).
% 3.37/1.55  tff(c_943, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_514, c_762, c_939])).
% 3.37/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.55  
% 3.37/1.55  Inference rules
% 3.37/1.55  ----------------------
% 3.37/1.55  #Ref     : 3
% 3.37/1.55  #Sup     : 165
% 3.37/1.55  #Fact    : 0
% 3.37/1.55  #Define  : 0
% 3.37/1.55  #Split   : 11
% 3.37/1.55  #Chain   : 0
% 3.37/1.55  #Close   : 0
% 3.37/1.55  
% 3.37/1.55  Ordering : KBO
% 3.37/1.55  
% 3.37/1.55  Simplification rules
% 3.37/1.55  ----------------------
% 3.37/1.55  #Subsume      : 14
% 3.37/1.55  #Demod        : 254
% 3.37/1.55  #Tautology    : 76
% 3.37/1.55  #SimpNegUnit  : 25
% 3.37/1.55  #BackRed      : 11
% 3.37/1.55  
% 3.37/1.55  #Partial instantiations: 0
% 3.37/1.55  #Strategies tried      : 1
% 3.37/1.55  
% 3.37/1.55  Timing (in seconds)
% 3.37/1.55  ----------------------
% 3.37/1.56  Preprocessing        : 0.35
% 3.37/1.56  Parsing              : 0.19
% 3.37/1.56  CNF conversion       : 0.02
% 3.37/1.56  Main loop            : 0.39
% 3.37/1.56  Inferencing          : 0.15
% 3.37/1.56  Reduction            : 0.12
% 3.37/1.56  Demodulation         : 0.08
% 3.37/1.56  BG Simplification    : 0.02
% 3.37/1.56  Subsumption          : 0.06
% 3.37/1.56  Abstraction          : 0.02
% 3.37/1.56  MUC search           : 0.00
% 3.37/1.56  Cooper               : 0.00
% 3.37/1.56  Total                : 0.80
% 3.37/1.56  Index Insertion      : 0.00
% 3.37/1.56  Index Deletion       : 0.00
% 3.37/1.56  Index Matching       : 0.00
% 3.37/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
