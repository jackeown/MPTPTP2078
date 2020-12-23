%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:58 EST 2020

% Result     : Theorem 7.83s
% Output     : CNFRefutation 7.83s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 951 expanded)
%              Number of leaves         :   32 ( 312 expanded)
%              Depth                    :   18
%              Number of atoms          :  374 (3269 expanded)
%              Number of equality atoms :   89 (1125 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
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

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_73,axiom,(
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

tff(f_91,axiom,(
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

tff(f_36,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_48,plain,
    ( k1_funct_1('#skF_5','#skF_7') != k1_funct_1('#skF_6','#skF_7')
    | ~ r1_partfun1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3124,plain,(
    ~ r1_partfun1('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_50,plain,
    ( r2_hidden('#skF_7',k1_relset_1('#skF_3','#skF_4','#skF_5'))
    | ~ r1_partfun1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_62,plain,(
    ~ r1_partfun1('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_76,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_84,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_76])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_83,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_76])).

tff(c_42,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_117,plain,(
    ! [A_60,B_61,C_62] :
      ( k1_relset_1(A_60,B_61,C_62) = k1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_125,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_117])).

tff(c_174,plain,(
    ! [A_70,B_71,C_72] :
      ( m1_subset_1(k1_relset_1(A_70,B_71,C_72),k1_zfmisc_1(A_70))
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_188,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_174])).

tff(c_196,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_188])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_89,plain,(
    ! [C_53,A_54,B_55] :
      ( r2_hidden(C_53,A_54)
      | ~ r2_hidden(C_53,B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_147,plain,(
    ! [A_65,B_66,A_67] :
      ( r2_hidden('#skF_1'(A_65,B_66),A_67)
      | ~ m1_subset_1(A_65,k1_zfmisc_1(A_67))
      | r1_tarski(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_6,c_89])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_163,plain,(
    ! [A_65,A_67] :
      ( ~ m1_subset_1(A_65,k1_zfmisc_1(A_67))
      | r1_tarski(A_65,A_67) ) ),
    inference(resolution,[status(thm)],[c_147,c_4])).

tff(c_202,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_196,c_163])).

tff(c_36,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_59,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_40,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_124,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_117])).

tff(c_480,plain,(
    ! [B_130,A_131,C_132] :
      ( k1_xboole_0 = B_130
      | k1_relset_1(A_131,B_130,C_132) = A_131
      | ~ v1_funct_2(C_132,A_131,B_130)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_131,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_487,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_480])).

tff(c_494,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_124,c_487])).

tff(c_495,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_494])).

tff(c_530,plain,(
    ! [A_133,B_134] :
      ( r2_hidden('#skF_2'(A_133,B_134),k1_relat_1(A_133))
      | r1_partfun1(A_133,B_134)
      | ~ r1_tarski(k1_relat_1(A_133),k1_relat_1(B_134))
      | ~ v1_funct_1(B_134)
      | ~ v1_relat_1(B_134)
      | ~ v1_funct_1(A_133)
      | ~ v1_relat_1(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_58,plain,(
    ! [E_40] :
      ( r1_partfun1('#skF_5','#skF_6')
      | k1_funct_1('#skF_5',E_40) = k1_funct_1('#skF_6',E_40)
      | ~ r2_hidden(E_40,k1_relset_1('#skF_3','#skF_4','#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_93,plain,(
    ! [E_40] :
      ( k1_funct_1('#skF_5',E_40) = k1_funct_1('#skF_6',E_40)
      | ~ r2_hidden(E_40,k1_relset_1('#skF_3','#skF_4','#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_58])).

tff(c_130,plain,(
    ! [E_40] :
      ( k1_funct_1('#skF_5',E_40) = k1_funct_1('#skF_6',E_40)
      | ~ r2_hidden(E_40,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_93])).

tff(c_534,plain,(
    ! [B_134] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',B_134)) = k1_funct_1('#skF_6','#skF_2'('#skF_5',B_134))
      | r1_partfun1('#skF_5',B_134)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_134))
      | ~ v1_funct_1(B_134)
      | ~ v1_relat_1(B_134)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_530,c_130])).

tff(c_1958,plain,(
    ! [B_337] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',B_337)) = k1_funct_1('#skF_6','#skF_2'('#skF_5',B_337))
      | r1_partfun1('#skF_5',B_337)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_337))
      | ~ v1_funct_1(B_337)
      | ~ v1_relat_1(B_337) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_46,c_534])).

tff(c_1967,plain,
    ( k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_5','#skF_6'))
    | r1_partfun1('#skF_5','#skF_6')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_495,c_1958])).

tff(c_1975,plain,
    ( k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_5','#skF_6'))
    | r1_partfun1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_42,c_202,c_1967])).

tff(c_1976,plain,(
    k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1975])).

tff(c_32,plain,(
    ! [B_29,A_23] :
      ( k1_funct_1(B_29,'#skF_2'(A_23,B_29)) != k1_funct_1(A_23,'#skF_2'(A_23,B_29))
      | r1_partfun1(A_23,B_29)
      | ~ r1_tarski(k1_relat_1(A_23),k1_relat_1(B_29))
      | ~ v1_funct_1(B_29)
      | ~ v1_relat_1(B_29)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1982,plain,
    ( r1_partfun1('#skF_5','#skF_6')
    | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1976,c_32])).

tff(c_1987,plain,(
    r1_partfun1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_46,c_83,c_42,c_202,c_495,c_1982])).

tff(c_1989,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1987])).

tff(c_1991,plain,(
    r1_partfun1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1993,plain,(
    k1_funct_1('#skF_5','#skF_7') != k1_funct_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1991,c_48])).

tff(c_2007,plain,(
    ! [C_341,A_342,B_343] :
      ( v1_relat_1(C_341)
      | ~ m1_subset_1(C_341,k1_zfmisc_1(k2_zfmisc_1(A_342,B_343))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2014,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_2007])).

tff(c_2052,plain,(
    ! [A_356,B_357,C_358] :
      ( k1_relset_1(A_356,B_357,C_358) = k1_relat_1(C_358)
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_zfmisc_1(A_356,B_357))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2060,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_2052])).

tff(c_2072,plain,(
    ! [A_359,B_360,C_361] :
      ( m1_subset_1(k1_relset_1(A_359,B_360,C_361),k1_zfmisc_1(A_359))
      | ~ m1_subset_1(C_361,k1_zfmisc_1(k2_zfmisc_1(A_359,B_360))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2083,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2060,c_2072])).

tff(c_2090,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2083])).

tff(c_2030,plain,(
    ! [C_348,A_349,B_350] :
      ( r2_hidden(C_348,A_349)
      | ~ r2_hidden(C_348,B_350)
      | ~ m1_subset_1(B_350,k1_zfmisc_1(A_349)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2168,plain,(
    ! [A_374,B_375,A_376] :
      ( r2_hidden('#skF_1'(A_374,B_375),A_376)
      | ~ m1_subset_1(A_374,k1_zfmisc_1(A_376))
      | r1_tarski(A_374,B_375) ) ),
    inference(resolution,[status(thm)],[c_6,c_2030])).

tff(c_2180,plain,(
    ! [A_377,A_378] :
      ( ~ m1_subset_1(A_377,k1_zfmisc_1(A_378))
      | r1_tarski(A_377,A_378) ) ),
    inference(resolution,[status(thm)],[c_2168,c_4])).

tff(c_2197,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_2090,c_2180])).

tff(c_2059,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_2052])).

tff(c_2328,plain,(
    ! [B_398,A_399,C_400] :
      ( k1_xboole_0 = B_398
      | k1_relset_1(A_399,B_398,C_400) = A_399
      | ~ v1_funct_2(C_400,A_399,B_398)
      | ~ m1_subset_1(C_400,k1_zfmisc_1(k2_zfmisc_1(A_399,B_398))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2335,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_2328])).

tff(c_2342,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2059,c_2335])).

tff(c_2343,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_2342])).

tff(c_2015,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_2007])).

tff(c_1990,plain,(
    r2_hidden('#skF_7',k1_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2067,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2060,c_1990])).

tff(c_2592,plain,(
    ! [B_431,C_432,A_433] :
      ( k1_funct_1(B_431,C_432) = k1_funct_1(A_433,C_432)
      | ~ r2_hidden(C_432,k1_relat_1(A_433))
      | ~ r1_partfun1(A_433,B_431)
      | ~ r1_tarski(k1_relat_1(A_433),k1_relat_1(B_431))
      | ~ v1_funct_1(B_431)
      | ~ v1_relat_1(B_431)
      | ~ v1_funct_1(A_433)
      | ~ v1_relat_1(A_433) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2607,plain,(
    ! [B_431] :
      ( k1_funct_1(B_431,'#skF_7') = k1_funct_1('#skF_5','#skF_7')
      | ~ r1_partfun1('#skF_5',B_431)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_431))
      | ~ v1_funct_1(B_431)
      | ~ v1_relat_1(B_431)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2067,c_2592])).

tff(c_3069,plain,(
    ! [B_521] :
      ( k1_funct_1(B_521,'#skF_7') = k1_funct_1('#skF_5','#skF_7')
      | ~ r1_partfun1('#skF_5',B_521)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_521))
      | ~ v1_funct_1(B_521)
      | ~ v1_relat_1(B_521) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2015,c_46,c_2607])).

tff(c_3072,plain,
    ( k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_6','#skF_7')
    | ~ r1_partfun1('#skF_5','#skF_6')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2343,c_3069])).

tff(c_3078,plain,(
    k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2014,c_42,c_2197,c_1991,c_3072])).

tff(c_3080,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1993,c_3078])).

tff(c_3082,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_3081,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_3087,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3082,c_3081])).

tff(c_3100,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3087,c_44])).

tff(c_3102,plain,(
    ! [C_525,A_526,B_527] :
      ( v1_relat_1(C_525)
      | ~ m1_subset_1(C_525,k1_zfmisc_1(k2_zfmisc_1(A_526,B_527))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3109,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3100,c_3102])).

tff(c_3099,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3087,c_38])).

tff(c_3110,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_3099,c_3102])).

tff(c_3111,plain,(
    ! [A_528,B_529] :
      ( r2_hidden('#skF_1'(A_528,B_529),A_528)
      | r1_tarski(A_528,B_529) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3116,plain,(
    ! [A_528] : r1_tarski(A_528,A_528) ),
    inference(resolution,[status(thm)],[c_3111,c_4])).

tff(c_3148,plain,(
    ! [A_541,B_542,C_543] :
      ( k1_relset_1(A_541,B_542,C_543) = k1_relat_1(C_543)
      | ~ m1_subset_1(C_543,k1_zfmisc_1(k2_zfmisc_1(A_541,B_542))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3155,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3100,c_3148])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16] :
      ( m1_subset_1(k1_relset_1(A_14,B_15,C_16),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3171,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3155,c_14])).

tff(c_3175,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3100,c_3171])).

tff(c_3130,plain,(
    ! [C_534,A_535,B_536] :
      ( r2_hidden(C_534,A_535)
      | ~ r2_hidden(C_534,B_536)
      | ~ m1_subset_1(B_536,k1_zfmisc_1(A_535)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3199,plain,(
    ! [A_548,B_549,A_550] :
      ( r2_hidden('#skF_1'(A_548,B_549),A_550)
      | ~ m1_subset_1(A_548,k1_zfmisc_1(A_550))
      | r1_tarski(A_548,B_549) ) ),
    inference(resolution,[status(thm)],[c_6,c_3130])).

tff(c_3216,plain,(
    ! [A_551,A_552] :
      ( ~ m1_subset_1(A_551,k1_zfmisc_1(A_552))
      | r1_tarski(A_551,A_552) ) ),
    inference(resolution,[status(thm)],[c_3199,c_4])).

tff(c_3233,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_3175,c_3216])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3097,plain,(
    ! [A_6] :
      ( A_6 = '#skF_4'
      | ~ r1_tarski(A_6,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3082,c_3082,c_8])).

tff(c_3271,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3233,c_3097])).

tff(c_3156,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_3099,c_3148])).

tff(c_3180,plain,
    ( m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3156,c_14])).

tff(c_3184,plain,(
    m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3099,c_3180])).

tff(c_3232,plain,(
    r1_tarski(k1_relat_1('#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_3184,c_3216])).

tff(c_3240,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3232,c_3097])).

tff(c_3725,plain,(
    ! [A_625,B_626] :
      ( r2_hidden('#skF_2'(A_625,B_626),k1_relat_1(A_625))
      | r1_partfun1(A_625,B_626)
      | ~ r1_tarski(k1_relat_1(A_625),k1_relat_1(B_626))
      | ~ v1_funct_1(B_626)
      | ~ v1_relat_1(B_626)
      | ~ v1_funct_1(A_625)
      | ~ v1_relat_1(A_625) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3732,plain,(
    ! [B_626] :
      ( r2_hidden('#skF_2'('#skF_5',B_626),'#skF_4')
      | r1_partfun1('#skF_5',B_626)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_626))
      | ~ v1_funct_1(B_626)
      | ~ v1_relat_1(B_626)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3271,c_3725])).

tff(c_3763,plain,(
    ! [B_629] :
      ( r2_hidden('#skF_2'('#skF_5',B_629),'#skF_4')
      | r1_partfun1('#skF_5',B_629)
      | ~ r1_tarski('#skF_4',k1_relat_1(B_629))
      | ~ v1_funct_1(B_629)
      | ~ v1_relat_1(B_629) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3109,c_46,c_3271,c_3732])).

tff(c_3186,plain,(
    ! [E_40] :
      ( r1_partfun1('#skF_5','#skF_6')
      | k1_funct_1('#skF_5',E_40) = k1_funct_1('#skF_6',E_40)
      | ~ r2_hidden(E_40,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3155,c_3087,c_58])).

tff(c_3187,plain,(
    ! [E_40] :
      ( k1_funct_1('#skF_5',E_40) = k1_funct_1('#skF_6',E_40)
      | ~ r2_hidden(E_40,k1_relat_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3124,c_3186])).

tff(c_3273,plain,(
    ! [E_40] :
      ( k1_funct_1('#skF_5',E_40) = k1_funct_1('#skF_6',E_40)
      | ~ r2_hidden(E_40,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3271,c_3187])).

tff(c_4226,plain,(
    ! [B_710] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_5',B_710)) = k1_funct_1('#skF_6','#skF_2'('#skF_5',B_710))
      | r1_partfun1('#skF_5',B_710)
      | ~ r1_tarski('#skF_4',k1_relat_1(B_710))
      | ~ v1_funct_1(B_710)
      | ~ v1_relat_1(B_710) ) ),
    inference(resolution,[status(thm)],[c_3763,c_3273])).

tff(c_4232,plain,
    ( k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_5','#skF_6'))
    | r1_partfun1('#skF_5','#skF_6')
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3240,c_4226])).

tff(c_4236,plain,
    ( k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_5','#skF_6'))
    | r1_partfun1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3110,c_42,c_3116,c_4232])).

tff(c_4237,plain,(
    k1_funct_1('#skF_5','#skF_2'('#skF_5','#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_3124,c_4236])).

tff(c_4240,plain,
    ( r1_partfun1('#skF_5','#skF_6')
    | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4237,c_32])).

tff(c_4245,plain,(
    r1_partfun1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3109,c_46,c_3110,c_42,c_3116,c_3271,c_3240,c_4240])).

tff(c_4247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3124,c_4245])).

tff(c_4248,plain,(
    k1_funct_1('#skF_5','#skF_7') != k1_funct_1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_4249,plain,(
    r1_partfun1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_3092,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3087,c_40])).

tff(c_4289,plain,(
    ! [A_723,B_724,C_725] :
      ( k1_relset_1(A_723,B_724,C_725) = k1_relat_1(C_725)
      | ~ m1_subset_1(C_725,k1_zfmisc_1(k2_zfmisc_1(A_723,B_724))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4297,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_3099,c_4289])).

tff(c_26,plain,(
    ! [B_21,C_22] :
      ( k1_relset_1(k1_xboole_0,B_21,C_22) = k1_xboole_0
      | ~ v1_funct_2(C_22,k1_xboole_0,B_21)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4515,plain,(
    ! [B_746,C_747] :
      ( k1_relset_1('#skF_4',B_746,C_747) = '#skF_4'
      | ~ v1_funct_2(C_747,'#skF_4',B_746)
      | ~ m1_subset_1(C_747,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_746))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3082,c_3082,c_3082,c_3082,c_26])).

tff(c_4525,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_3099,c_4515])).

tff(c_4532,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3092,c_4297,c_4525])).

tff(c_4296,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3100,c_4289])).

tff(c_4315,plain,(
    ! [A_726,B_727,C_728] :
      ( m1_subset_1(k1_relset_1(A_726,B_727,C_728),k1_zfmisc_1(A_726))
      | ~ m1_subset_1(C_728,k1_zfmisc_1(k2_zfmisc_1(A_726,B_727))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4329,plain,
    ( m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4296,c_4315])).

tff(c_4335,plain,(
    m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3100,c_4329])).

tff(c_4255,plain,(
    r2_hidden('#skF_7',k1_relset_1('#skF_4','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4249,c_3087,c_50])).

tff(c_4259,plain,(
    ! [C_714,A_715,B_716] :
      ( r2_hidden(C_714,A_715)
      | ~ r2_hidden(C_714,B_716)
      | ~ m1_subset_1(B_716,k1_zfmisc_1(A_715)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4264,plain,(
    ! [A_715] :
      ( r2_hidden('#skF_7',A_715)
      | ~ m1_subset_1(k1_relset_1('#skF_4','#skF_4','#skF_5'),k1_zfmisc_1(A_715)) ) ),
    inference(resolution,[status(thm)],[c_4255,c_4259])).

tff(c_4344,plain,(
    ! [A_730] :
      ( r2_hidden('#skF_7',A_730)
      | ~ m1_subset_1(k1_relat_1('#skF_5'),k1_zfmisc_1(A_730)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4296,c_4264])).

tff(c_4348,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_4335,c_4344])).

tff(c_22,plain,(
    ! [C_22,B_21] :
      ( v1_funct_2(C_22,k1_xboole_0,B_21)
      | k1_relset_1(k1_xboole_0,B_21,C_22) != k1_xboole_0
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4425,plain,(
    ! [C_742,B_743] :
      ( v1_funct_2(C_742,'#skF_4',B_743)
      | k1_relset_1('#skF_4',B_743,C_742) != '#skF_4'
      | ~ m1_subset_1(C_742,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_743))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3082,c_3082,c_3082,c_3082,c_22])).

tff(c_4432,plain,
    ( v1_funct_2('#skF_5','#skF_4','#skF_4')
    | k1_relset_1('#skF_4','#skF_4','#skF_5') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_3100,c_4425])).

tff(c_4438,plain,
    ( v1_funct_2('#skF_5','#skF_4','#skF_4')
    | k1_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4296,c_4432])).

tff(c_4441,plain,(
    k1_relat_1('#skF_5') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4438])).

tff(c_4412,plain,(
    ! [A_739,B_740,A_741] :
      ( r2_hidden('#skF_1'(A_739,B_740),A_741)
      | ~ m1_subset_1(A_739,k1_zfmisc_1(A_741))
      | r1_tarski(A_739,B_740) ) ),
    inference(resolution,[status(thm)],[c_6,c_4259])).

tff(c_4442,plain,(
    ! [A_744,A_745] :
      ( ~ m1_subset_1(A_744,k1_zfmisc_1(A_745))
      | r1_tarski(A_744,A_745) ) ),
    inference(resolution,[status(thm)],[c_4412,c_4])).

tff(c_4458,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_4335,c_4442])).

tff(c_4473,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4458,c_3097])).

tff(c_4481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4441,c_4473])).

tff(c_4483,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4438])).

tff(c_4985,plain,(
    ! [B_822,C_823,A_824] :
      ( k1_funct_1(B_822,C_823) = k1_funct_1(A_824,C_823)
      | ~ r2_hidden(C_823,k1_relat_1(A_824))
      | ~ r1_partfun1(A_824,B_822)
      | ~ r1_tarski(k1_relat_1(A_824),k1_relat_1(B_822))
      | ~ v1_funct_1(B_822)
      | ~ v1_relat_1(B_822)
      | ~ v1_funct_1(A_824)
      | ~ v1_relat_1(A_824) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4997,plain,(
    ! [B_822,C_823] :
      ( k1_funct_1(B_822,C_823) = k1_funct_1('#skF_5',C_823)
      | ~ r2_hidden(C_823,'#skF_4')
      | ~ r1_partfun1('#skF_5',B_822)
      | ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1(B_822))
      | ~ v1_funct_1(B_822)
      | ~ v1_relat_1(B_822)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4483,c_4985])).

tff(c_5406,plain,(
    ! [B_914,C_915] :
      ( k1_funct_1(B_914,C_915) = k1_funct_1('#skF_5',C_915)
      | ~ r2_hidden(C_915,'#skF_4')
      | ~ r1_partfun1('#skF_5',B_914)
      | ~ r1_tarski('#skF_4',k1_relat_1(B_914))
      | ~ v1_funct_1(B_914)
      | ~ v1_relat_1(B_914) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3109,c_46,c_4483,c_4997])).

tff(c_5482,plain,(
    ! [B_916] :
      ( k1_funct_1(B_916,'#skF_7') = k1_funct_1('#skF_5','#skF_7')
      | ~ r1_partfun1('#skF_5',B_916)
      | ~ r1_tarski('#skF_4',k1_relat_1(B_916))
      | ~ v1_funct_1(B_916)
      | ~ v1_relat_1(B_916) ) ),
    inference(resolution,[status(thm)],[c_4348,c_5406])).

tff(c_5485,plain,
    ( k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_6','#skF_7')
    | ~ r1_partfun1('#skF_5','#skF_6')
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4532,c_5482])).

tff(c_5490,plain,(
    k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3110,c_42,c_3116,c_4249,c_5485])).

tff(c_5492,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4248,c_5490])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:28:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.83/2.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.83/2.66  
% 7.83/2.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.83/2.66  %$ v1_funct_2 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 7.83/2.66  
% 7.83/2.66  %Foreground sorts:
% 7.83/2.66  
% 7.83/2.66  
% 7.83/2.66  %Background operators:
% 7.83/2.66  
% 7.83/2.66  
% 7.83/2.66  %Foreground operators:
% 7.83/2.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.83/2.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.83/2.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.83/2.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.83/2.66  tff('#skF_7', type, '#skF_7': $i).
% 7.83/2.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.83/2.66  tff('#skF_5', type, '#skF_5': $i).
% 7.83/2.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.83/2.66  tff('#skF_6', type, '#skF_6': $i).
% 7.83/2.66  tff('#skF_3', type, '#skF_3': $i).
% 7.83/2.66  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.83/2.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.83/2.66  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.83/2.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.83/2.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.83/2.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.83/2.66  tff('#skF_4', type, '#skF_4': $i).
% 7.83/2.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.83/2.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.83/2.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.83/2.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.83/2.66  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 7.83/2.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.83/2.66  
% 7.83/2.69  tff(f_114, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (r1_partfun1(C, D) <=> (![E]: (r2_hidden(E, k1_relset_1(A, B, C)) => (k1_funct_1(C, E) = k1_funct_1(D, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_2)).
% 7.83/2.69  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.83/2.69  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.83/2.69  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 7.83/2.69  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.83/2.69  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 7.83/2.69  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.83/2.69  tff(f_91, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) => (r1_partfun1(A, B) <=> (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_partfun1)).
% 7.83/2.69  tff(f_36, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 7.83/2.69  tff(c_48, plain, (k1_funct_1('#skF_5', '#skF_7')!=k1_funct_1('#skF_6', '#skF_7') | ~r1_partfun1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.83/2.69  tff(c_3124, plain, (~r1_partfun1('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_48])).
% 7.83/2.69  tff(c_50, plain, (r2_hidden('#skF_7', k1_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~r1_partfun1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.83/2.69  tff(c_62, plain, (~r1_partfun1('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_50])).
% 7.83/2.69  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.83/2.69  tff(c_76, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.83/2.69  tff(c_84, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_76])).
% 7.83/2.69  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.83/2.69  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.83/2.69  tff(c_83, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_76])).
% 7.83/2.69  tff(c_42, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.83/2.69  tff(c_117, plain, (![A_60, B_61, C_62]: (k1_relset_1(A_60, B_61, C_62)=k1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.83/2.69  tff(c_125, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_117])).
% 7.83/2.69  tff(c_174, plain, (![A_70, B_71, C_72]: (m1_subset_1(k1_relset_1(A_70, B_71, C_72), k1_zfmisc_1(A_70)) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.83/2.69  tff(c_188, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_125, c_174])).
% 7.83/2.69  tff(c_196, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_188])).
% 7.83/2.69  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.83/2.69  tff(c_89, plain, (![C_53, A_54, B_55]: (r2_hidden(C_53, A_54) | ~r2_hidden(C_53, B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.83/2.69  tff(c_147, plain, (![A_65, B_66, A_67]: (r2_hidden('#skF_1'(A_65, B_66), A_67) | ~m1_subset_1(A_65, k1_zfmisc_1(A_67)) | r1_tarski(A_65, B_66))), inference(resolution, [status(thm)], [c_6, c_89])).
% 7.83/2.69  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.83/2.69  tff(c_163, plain, (![A_65, A_67]: (~m1_subset_1(A_65, k1_zfmisc_1(A_67)) | r1_tarski(A_65, A_67))), inference(resolution, [status(thm)], [c_147, c_4])).
% 7.83/2.69  tff(c_202, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_196, c_163])).
% 7.83/2.69  tff(c_36, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.83/2.69  tff(c_59, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_36])).
% 7.83/2.69  tff(c_40, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.83/2.69  tff(c_124, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_117])).
% 7.83/2.69  tff(c_480, plain, (![B_130, A_131, C_132]: (k1_xboole_0=B_130 | k1_relset_1(A_131, B_130, C_132)=A_131 | ~v1_funct_2(C_132, A_131, B_130) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_131, B_130))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.83/2.69  tff(c_487, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_480])).
% 7.83/2.69  tff(c_494, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_124, c_487])).
% 7.83/2.69  tff(c_495, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_59, c_494])).
% 7.83/2.69  tff(c_530, plain, (![A_133, B_134]: (r2_hidden('#skF_2'(A_133, B_134), k1_relat_1(A_133)) | r1_partfun1(A_133, B_134) | ~r1_tarski(k1_relat_1(A_133), k1_relat_1(B_134)) | ~v1_funct_1(B_134) | ~v1_relat_1(B_134) | ~v1_funct_1(A_133) | ~v1_relat_1(A_133))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.83/2.69  tff(c_58, plain, (![E_40]: (r1_partfun1('#skF_5', '#skF_6') | k1_funct_1('#skF_5', E_40)=k1_funct_1('#skF_6', E_40) | ~r2_hidden(E_40, k1_relset_1('#skF_3', '#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.83/2.69  tff(c_93, plain, (![E_40]: (k1_funct_1('#skF_5', E_40)=k1_funct_1('#skF_6', E_40) | ~r2_hidden(E_40, k1_relset_1('#skF_3', '#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_62, c_58])).
% 7.83/2.69  tff(c_130, plain, (![E_40]: (k1_funct_1('#skF_5', E_40)=k1_funct_1('#skF_6', E_40) | ~r2_hidden(E_40, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_93])).
% 7.83/2.69  tff(c_534, plain, (![B_134]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', B_134))=k1_funct_1('#skF_6', '#skF_2'('#skF_5', B_134)) | r1_partfun1('#skF_5', B_134) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_134)) | ~v1_funct_1(B_134) | ~v1_relat_1(B_134) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_530, c_130])).
% 7.83/2.69  tff(c_1958, plain, (![B_337]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', B_337))=k1_funct_1('#skF_6', '#skF_2'('#skF_5', B_337)) | r1_partfun1('#skF_5', B_337) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_337)) | ~v1_funct_1(B_337) | ~v1_relat_1(B_337))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_46, c_534])).
% 7.83/2.69  tff(c_1967, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_5', '#skF_6')) | r1_partfun1('#skF_5', '#skF_6') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_495, c_1958])).
% 7.83/2.69  tff(c_1975, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_5', '#skF_6')) | r1_partfun1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_42, c_202, c_1967])).
% 7.83/2.69  tff(c_1976, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_62, c_1975])).
% 7.83/2.69  tff(c_32, plain, (![B_29, A_23]: (k1_funct_1(B_29, '#skF_2'(A_23, B_29))!=k1_funct_1(A_23, '#skF_2'(A_23, B_29)) | r1_partfun1(A_23, B_29) | ~r1_tarski(k1_relat_1(A_23), k1_relat_1(B_29)) | ~v1_funct_1(B_29) | ~v1_relat_1(B_29) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.83/2.69  tff(c_1982, plain, (r1_partfun1('#skF_5', '#skF_6') | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1976, c_32])).
% 7.83/2.69  tff(c_1987, plain, (r1_partfun1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_46, c_83, c_42, c_202, c_495, c_1982])).
% 7.83/2.69  tff(c_1989, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1987])).
% 7.83/2.69  tff(c_1991, plain, (r1_partfun1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_50])).
% 7.83/2.69  tff(c_1993, plain, (k1_funct_1('#skF_5', '#skF_7')!=k1_funct_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1991, c_48])).
% 7.83/2.69  tff(c_2007, plain, (![C_341, A_342, B_343]: (v1_relat_1(C_341) | ~m1_subset_1(C_341, k1_zfmisc_1(k2_zfmisc_1(A_342, B_343))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.83/2.69  tff(c_2014, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_2007])).
% 7.83/2.69  tff(c_2052, plain, (![A_356, B_357, C_358]: (k1_relset_1(A_356, B_357, C_358)=k1_relat_1(C_358) | ~m1_subset_1(C_358, k1_zfmisc_1(k2_zfmisc_1(A_356, B_357))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.83/2.69  tff(c_2060, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_2052])).
% 7.83/2.69  tff(c_2072, plain, (![A_359, B_360, C_361]: (m1_subset_1(k1_relset_1(A_359, B_360, C_361), k1_zfmisc_1(A_359)) | ~m1_subset_1(C_361, k1_zfmisc_1(k2_zfmisc_1(A_359, B_360))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.83/2.69  tff(c_2083, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2060, c_2072])).
% 7.83/2.69  tff(c_2090, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2083])).
% 7.83/2.69  tff(c_2030, plain, (![C_348, A_349, B_350]: (r2_hidden(C_348, A_349) | ~r2_hidden(C_348, B_350) | ~m1_subset_1(B_350, k1_zfmisc_1(A_349)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.83/2.69  tff(c_2168, plain, (![A_374, B_375, A_376]: (r2_hidden('#skF_1'(A_374, B_375), A_376) | ~m1_subset_1(A_374, k1_zfmisc_1(A_376)) | r1_tarski(A_374, B_375))), inference(resolution, [status(thm)], [c_6, c_2030])).
% 7.83/2.69  tff(c_2180, plain, (![A_377, A_378]: (~m1_subset_1(A_377, k1_zfmisc_1(A_378)) | r1_tarski(A_377, A_378))), inference(resolution, [status(thm)], [c_2168, c_4])).
% 7.83/2.69  tff(c_2197, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_2090, c_2180])).
% 7.83/2.69  tff(c_2059, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_2052])).
% 7.83/2.69  tff(c_2328, plain, (![B_398, A_399, C_400]: (k1_xboole_0=B_398 | k1_relset_1(A_399, B_398, C_400)=A_399 | ~v1_funct_2(C_400, A_399, B_398) | ~m1_subset_1(C_400, k1_zfmisc_1(k2_zfmisc_1(A_399, B_398))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.83/2.69  tff(c_2335, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_2328])).
% 7.83/2.69  tff(c_2342, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2059, c_2335])).
% 7.83/2.69  tff(c_2343, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_59, c_2342])).
% 7.83/2.69  tff(c_2015, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_2007])).
% 7.83/2.69  tff(c_1990, plain, (r2_hidden('#skF_7', k1_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_50])).
% 7.83/2.69  tff(c_2067, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2060, c_1990])).
% 7.83/2.69  tff(c_2592, plain, (![B_431, C_432, A_433]: (k1_funct_1(B_431, C_432)=k1_funct_1(A_433, C_432) | ~r2_hidden(C_432, k1_relat_1(A_433)) | ~r1_partfun1(A_433, B_431) | ~r1_tarski(k1_relat_1(A_433), k1_relat_1(B_431)) | ~v1_funct_1(B_431) | ~v1_relat_1(B_431) | ~v1_funct_1(A_433) | ~v1_relat_1(A_433))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.83/2.69  tff(c_2607, plain, (![B_431]: (k1_funct_1(B_431, '#skF_7')=k1_funct_1('#skF_5', '#skF_7') | ~r1_partfun1('#skF_5', B_431) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_431)) | ~v1_funct_1(B_431) | ~v1_relat_1(B_431) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_2067, c_2592])).
% 7.83/2.69  tff(c_3069, plain, (![B_521]: (k1_funct_1(B_521, '#skF_7')=k1_funct_1('#skF_5', '#skF_7') | ~r1_partfun1('#skF_5', B_521) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_521)) | ~v1_funct_1(B_521) | ~v1_relat_1(B_521))), inference(demodulation, [status(thm), theory('equality')], [c_2015, c_46, c_2607])).
% 7.83/2.69  tff(c_3072, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_6', '#skF_7') | ~r1_partfun1('#skF_5', '#skF_6') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2343, c_3069])).
% 7.83/2.69  tff(c_3078, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2014, c_42, c_2197, c_1991, c_3072])).
% 7.83/2.69  tff(c_3080, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1993, c_3078])).
% 7.83/2.69  tff(c_3082, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_36])).
% 7.83/2.69  tff(c_3081, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_36])).
% 7.83/2.69  tff(c_3087, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3082, c_3081])).
% 7.83/2.69  tff(c_3100, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_3087, c_44])).
% 7.83/2.69  tff(c_3102, plain, (![C_525, A_526, B_527]: (v1_relat_1(C_525) | ~m1_subset_1(C_525, k1_zfmisc_1(k2_zfmisc_1(A_526, B_527))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.83/2.69  tff(c_3109, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_3100, c_3102])).
% 7.83/2.69  tff(c_3099, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_3087, c_38])).
% 7.83/2.69  tff(c_3110, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_3099, c_3102])).
% 7.83/2.69  tff(c_3111, plain, (![A_528, B_529]: (r2_hidden('#skF_1'(A_528, B_529), A_528) | r1_tarski(A_528, B_529))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.83/2.69  tff(c_3116, plain, (![A_528]: (r1_tarski(A_528, A_528))), inference(resolution, [status(thm)], [c_3111, c_4])).
% 7.83/2.69  tff(c_3148, plain, (![A_541, B_542, C_543]: (k1_relset_1(A_541, B_542, C_543)=k1_relat_1(C_543) | ~m1_subset_1(C_543, k1_zfmisc_1(k2_zfmisc_1(A_541, B_542))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.83/2.69  tff(c_3155, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_3100, c_3148])).
% 7.83/2.69  tff(c_14, plain, (![A_14, B_15, C_16]: (m1_subset_1(k1_relset_1(A_14, B_15, C_16), k1_zfmisc_1(A_14)) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.83/2.69  tff(c_3171, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_3155, c_14])).
% 7.83/2.69  tff(c_3175, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3100, c_3171])).
% 7.83/2.69  tff(c_3130, plain, (![C_534, A_535, B_536]: (r2_hidden(C_534, A_535) | ~r2_hidden(C_534, B_536) | ~m1_subset_1(B_536, k1_zfmisc_1(A_535)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.83/2.69  tff(c_3199, plain, (![A_548, B_549, A_550]: (r2_hidden('#skF_1'(A_548, B_549), A_550) | ~m1_subset_1(A_548, k1_zfmisc_1(A_550)) | r1_tarski(A_548, B_549))), inference(resolution, [status(thm)], [c_6, c_3130])).
% 7.83/2.69  tff(c_3216, plain, (![A_551, A_552]: (~m1_subset_1(A_551, k1_zfmisc_1(A_552)) | r1_tarski(A_551, A_552))), inference(resolution, [status(thm)], [c_3199, c_4])).
% 7.83/2.69  tff(c_3233, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_3175, c_3216])).
% 7.83/2.69  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.83/2.69  tff(c_3097, plain, (![A_6]: (A_6='#skF_4' | ~r1_tarski(A_6, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3082, c_3082, c_8])).
% 7.83/2.69  tff(c_3271, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_3233, c_3097])).
% 7.83/2.69  tff(c_3156, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_3099, c_3148])).
% 7.83/2.69  tff(c_3180, plain, (m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_3156, c_14])).
% 7.83/2.69  tff(c_3184, plain, (m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3099, c_3180])).
% 7.83/2.69  tff(c_3232, plain, (r1_tarski(k1_relat_1('#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_3184, c_3216])).
% 7.83/2.69  tff(c_3240, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(resolution, [status(thm)], [c_3232, c_3097])).
% 7.83/2.69  tff(c_3725, plain, (![A_625, B_626]: (r2_hidden('#skF_2'(A_625, B_626), k1_relat_1(A_625)) | r1_partfun1(A_625, B_626) | ~r1_tarski(k1_relat_1(A_625), k1_relat_1(B_626)) | ~v1_funct_1(B_626) | ~v1_relat_1(B_626) | ~v1_funct_1(A_625) | ~v1_relat_1(A_625))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.83/2.69  tff(c_3732, plain, (![B_626]: (r2_hidden('#skF_2'('#skF_5', B_626), '#skF_4') | r1_partfun1('#skF_5', B_626) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_626)) | ~v1_funct_1(B_626) | ~v1_relat_1(B_626) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3271, c_3725])).
% 7.83/2.69  tff(c_3763, plain, (![B_629]: (r2_hidden('#skF_2'('#skF_5', B_629), '#skF_4') | r1_partfun1('#skF_5', B_629) | ~r1_tarski('#skF_4', k1_relat_1(B_629)) | ~v1_funct_1(B_629) | ~v1_relat_1(B_629))), inference(demodulation, [status(thm), theory('equality')], [c_3109, c_46, c_3271, c_3732])).
% 7.83/2.69  tff(c_3186, plain, (![E_40]: (r1_partfun1('#skF_5', '#skF_6') | k1_funct_1('#skF_5', E_40)=k1_funct_1('#skF_6', E_40) | ~r2_hidden(E_40, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_3155, c_3087, c_58])).
% 7.83/2.69  tff(c_3187, plain, (![E_40]: (k1_funct_1('#skF_5', E_40)=k1_funct_1('#skF_6', E_40) | ~r2_hidden(E_40, k1_relat_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_3124, c_3186])).
% 7.83/2.69  tff(c_3273, plain, (![E_40]: (k1_funct_1('#skF_5', E_40)=k1_funct_1('#skF_6', E_40) | ~r2_hidden(E_40, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3271, c_3187])).
% 7.83/2.69  tff(c_4226, plain, (![B_710]: (k1_funct_1('#skF_5', '#skF_2'('#skF_5', B_710))=k1_funct_1('#skF_6', '#skF_2'('#skF_5', B_710)) | r1_partfun1('#skF_5', B_710) | ~r1_tarski('#skF_4', k1_relat_1(B_710)) | ~v1_funct_1(B_710) | ~v1_relat_1(B_710))), inference(resolution, [status(thm)], [c_3763, c_3273])).
% 7.83/2.69  tff(c_4232, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_5', '#skF_6')) | r1_partfun1('#skF_5', '#skF_6') | ~r1_tarski('#skF_4', '#skF_4') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3240, c_4226])).
% 7.83/2.69  tff(c_4236, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_5', '#skF_6')) | r1_partfun1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3110, c_42, c_3116, c_4232])).
% 7.83/2.69  tff(c_4237, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_5', '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_3124, c_4236])).
% 7.83/2.69  tff(c_4240, plain, (r1_partfun1('#skF_5', '#skF_6') | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4237, c_32])).
% 7.83/2.69  tff(c_4245, plain, (r1_partfun1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3109, c_46, c_3110, c_42, c_3116, c_3271, c_3240, c_4240])).
% 7.83/2.69  tff(c_4247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3124, c_4245])).
% 7.83/2.69  tff(c_4248, plain, (k1_funct_1('#skF_5', '#skF_7')!=k1_funct_1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_48])).
% 7.83/2.69  tff(c_4249, plain, (r1_partfun1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_48])).
% 7.83/2.69  tff(c_3092, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3087, c_40])).
% 7.83/2.69  tff(c_4289, plain, (![A_723, B_724, C_725]: (k1_relset_1(A_723, B_724, C_725)=k1_relat_1(C_725) | ~m1_subset_1(C_725, k1_zfmisc_1(k2_zfmisc_1(A_723, B_724))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.83/2.69  tff(c_4297, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_3099, c_4289])).
% 7.83/2.69  tff(c_26, plain, (![B_21, C_22]: (k1_relset_1(k1_xboole_0, B_21, C_22)=k1_xboole_0 | ~v1_funct_2(C_22, k1_xboole_0, B_21) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_21))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.83/2.69  tff(c_4515, plain, (![B_746, C_747]: (k1_relset_1('#skF_4', B_746, C_747)='#skF_4' | ~v1_funct_2(C_747, '#skF_4', B_746) | ~m1_subset_1(C_747, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_746))))), inference(demodulation, [status(thm), theory('equality')], [c_3082, c_3082, c_3082, c_3082, c_26])).
% 7.83/2.69  tff(c_4525, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_3099, c_4515])).
% 7.83/2.69  tff(c_4532, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3092, c_4297, c_4525])).
% 7.83/2.69  tff(c_4296, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_3100, c_4289])).
% 7.83/2.69  tff(c_4315, plain, (![A_726, B_727, C_728]: (m1_subset_1(k1_relset_1(A_726, B_727, C_728), k1_zfmisc_1(A_726)) | ~m1_subset_1(C_728, k1_zfmisc_1(k2_zfmisc_1(A_726, B_727))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.83/2.69  tff(c_4329, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_4296, c_4315])).
% 7.83/2.69  tff(c_4335, plain, (m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3100, c_4329])).
% 7.83/2.69  tff(c_4255, plain, (r2_hidden('#skF_7', k1_relset_1('#skF_4', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4249, c_3087, c_50])).
% 7.83/2.69  tff(c_4259, plain, (![C_714, A_715, B_716]: (r2_hidden(C_714, A_715) | ~r2_hidden(C_714, B_716) | ~m1_subset_1(B_716, k1_zfmisc_1(A_715)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.83/2.69  tff(c_4264, plain, (![A_715]: (r2_hidden('#skF_7', A_715) | ~m1_subset_1(k1_relset_1('#skF_4', '#skF_4', '#skF_5'), k1_zfmisc_1(A_715)))), inference(resolution, [status(thm)], [c_4255, c_4259])).
% 7.83/2.69  tff(c_4344, plain, (![A_730]: (r2_hidden('#skF_7', A_730) | ~m1_subset_1(k1_relat_1('#skF_5'), k1_zfmisc_1(A_730)))), inference(demodulation, [status(thm), theory('equality')], [c_4296, c_4264])).
% 7.83/2.69  tff(c_4348, plain, (r2_hidden('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_4335, c_4344])).
% 7.83/2.69  tff(c_22, plain, (![C_22, B_21]: (v1_funct_2(C_22, k1_xboole_0, B_21) | k1_relset_1(k1_xboole_0, B_21, C_22)!=k1_xboole_0 | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_21))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.83/2.69  tff(c_4425, plain, (![C_742, B_743]: (v1_funct_2(C_742, '#skF_4', B_743) | k1_relset_1('#skF_4', B_743, C_742)!='#skF_4' | ~m1_subset_1(C_742, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_743))))), inference(demodulation, [status(thm), theory('equality')], [c_3082, c_3082, c_3082, c_3082, c_22])).
% 7.83/2.69  tff(c_4432, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4') | k1_relset_1('#skF_4', '#skF_4', '#skF_5')!='#skF_4'), inference(resolution, [status(thm)], [c_3100, c_4425])).
% 7.83/2.69  tff(c_4438, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4') | k1_relat_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4296, c_4432])).
% 7.83/2.69  tff(c_4441, plain, (k1_relat_1('#skF_5')!='#skF_4'), inference(splitLeft, [status(thm)], [c_4438])).
% 7.83/2.69  tff(c_4412, plain, (![A_739, B_740, A_741]: (r2_hidden('#skF_1'(A_739, B_740), A_741) | ~m1_subset_1(A_739, k1_zfmisc_1(A_741)) | r1_tarski(A_739, B_740))), inference(resolution, [status(thm)], [c_6, c_4259])).
% 7.83/2.69  tff(c_4442, plain, (![A_744, A_745]: (~m1_subset_1(A_744, k1_zfmisc_1(A_745)) | r1_tarski(A_744, A_745))), inference(resolution, [status(thm)], [c_4412, c_4])).
% 7.83/2.69  tff(c_4458, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_4335, c_4442])).
% 7.83/2.69  tff(c_4473, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_4458, c_3097])).
% 7.83/2.69  tff(c_4481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4441, c_4473])).
% 7.83/2.69  tff(c_4483, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_4438])).
% 7.83/2.69  tff(c_4985, plain, (![B_822, C_823, A_824]: (k1_funct_1(B_822, C_823)=k1_funct_1(A_824, C_823) | ~r2_hidden(C_823, k1_relat_1(A_824)) | ~r1_partfun1(A_824, B_822) | ~r1_tarski(k1_relat_1(A_824), k1_relat_1(B_822)) | ~v1_funct_1(B_822) | ~v1_relat_1(B_822) | ~v1_funct_1(A_824) | ~v1_relat_1(A_824))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.83/2.69  tff(c_4997, plain, (![B_822, C_823]: (k1_funct_1(B_822, C_823)=k1_funct_1('#skF_5', C_823) | ~r2_hidden(C_823, '#skF_4') | ~r1_partfun1('#skF_5', B_822) | ~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1(B_822)) | ~v1_funct_1(B_822) | ~v1_relat_1(B_822) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4483, c_4985])).
% 7.83/2.69  tff(c_5406, plain, (![B_914, C_915]: (k1_funct_1(B_914, C_915)=k1_funct_1('#skF_5', C_915) | ~r2_hidden(C_915, '#skF_4') | ~r1_partfun1('#skF_5', B_914) | ~r1_tarski('#skF_4', k1_relat_1(B_914)) | ~v1_funct_1(B_914) | ~v1_relat_1(B_914))), inference(demodulation, [status(thm), theory('equality')], [c_3109, c_46, c_4483, c_4997])).
% 7.83/2.69  tff(c_5482, plain, (![B_916]: (k1_funct_1(B_916, '#skF_7')=k1_funct_1('#skF_5', '#skF_7') | ~r1_partfun1('#skF_5', B_916) | ~r1_tarski('#skF_4', k1_relat_1(B_916)) | ~v1_funct_1(B_916) | ~v1_relat_1(B_916))), inference(resolution, [status(thm)], [c_4348, c_5406])).
% 7.83/2.69  tff(c_5485, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_6', '#skF_7') | ~r1_partfun1('#skF_5', '#skF_6') | ~r1_tarski('#skF_4', '#skF_4') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4532, c_5482])).
% 7.83/2.69  tff(c_5490, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3110, c_42, c_3116, c_4249, c_5485])).
% 7.83/2.69  tff(c_5492, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4248, c_5490])).
% 7.83/2.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.83/2.69  
% 7.83/2.69  Inference rules
% 7.83/2.69  ----------------------
% 7.83/2.69  #Ref     : 4
% 7.83/2.69  #Sup     : 1312
% 7.83/2.69  #Fact    : 0
% 7.83/2.69  #Define  : 0
% 7.83/2.69  #Split   : 67
% 7.83/2.69  #Chain   : 0
% 7.83/2.69  #Close   : 0
% 7.83/2.69  
% 7.83/2.69  Ordering : KBO
% 7.83/2.69  
% 7.83/2.69  Simplification rules
% 8.21/2.69  ----------------------
% 8.21/2.69  #Subsume      : 482
% 8.21/2.69  #Demod        : 461
% 8.21/2.69  #Tautology    : 153
% 8.21/2.69  #SimpNegUnit  : 18
% 8.21/2.69  #BackRed      : 32
% 8.21/2.69  
% 8.21/2.69  #Partial instantiations: 0
% 8.21/2.69  #Strategies tried      : 1
% 8.21/2.69  
% 8.21/2.69  Timing (in seconds)
% 8.21/2.69  ----------------------
% 8.21/2.69  Preprocessing        : 0.32
% 8.21/2.69  Parsing              : 0.16
% 8.21/2.69  CNF conversion       : 0.02
% 8.21/2.69  Main loop            : 1.54
% 8.21/2.69  Inferencing          : 0.49
% 8.21/2.69  Reduction            : 0.45
% 8.21/2.69  Demodulation         : 0.29
% 8.21/2.69  BG Simplification    : 0.05
% 8.21/2.69  Subsumption          : 0.44
% 8.21/2.69  Abstraction          : 0.07
% 8.21/2.69  MUC search           : 0.00
% 8.21/2.69  Cooper               : 0.00
% 8.21/2.69  Total                : 1.92
% 8.21/2.69  Index Insertion      : 0.00
% 8.21/2.69  Index Deletion       : 0.00
% 8.21/2.69  Index Matching       : 0.00
% 8.21/2.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
