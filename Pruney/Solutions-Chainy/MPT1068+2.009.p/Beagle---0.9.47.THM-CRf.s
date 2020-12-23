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
% DateTime   : Thu Dec  3 10:17:42 EST 2020

% Result     : Theorem 49.68s
% Output     : CNFRefutation 50.04s
% Verified   : 
% Statistics : Number of formulae       :  353 (3406 expanded)
%              Number of leaves         :   45 (1116 expanded)
%              Depth                    :   21
%              Number of atoms          :  822 (11900 expanded)
%              Number of equality atoms :  202 (3896 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_164,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_38,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_129,axiom,(
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

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_139,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_111,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( r1_tarski(k2_relset_1(A,B,D),k1_relset_1(B,C,E))
           => ( B = k1_xboole_0
              | k8_funct_2(A,B,C,D,E) = k1_partfun1(A,B,B,C,D,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_2)).

tff(f_80,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_6,plain,(
    ! [A_5] : m1_subset_1('#skF_1'(A_5),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_56,plain,(
    m1_subset_1('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_99,plain,(
    ! [C_68,A_69,B_70] :
      ( v1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_120,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_99])).

tff(c_60,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_64,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_588,plain,(
    ! [A_131,B_132,C_133] :
      ( k1_relset_1(A_131,B_132,C_133) = k1_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_608,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_588])).

tff(c_4358,plain,(
    ! [B_370,A_371,C_372] :
      ( k1_xboole_0 = B_370
      | k1_relset_1(A_371,B_370,C_372) = A_371
      | ~ v1_funct_2(C_372,A_371,B_370)
      | ~ m1_subset_1(C_372,k1_zfmisc_1(k2_zfmisc_1(A_371,B_370))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_4365,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_4358])).

tff(c_4380,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_608,c_4365])).

tff(c_4435,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4380])).

tff(c_119,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_99])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_227453,plain,(
    ! [B_7161,C_7162,A_7163] :
      ( k1_funct_1(k5_relat_1(B_7161,C_7162),A_7163) = k1_funct_1(C_7162,k1_funct_1(B_7161,A_7163))
      | ~ r2_hidden(A_7163,k1_relat_1(B_7161))
      | ~ v1_funct_1(C_7162)
      | ~ v1_relat_1(C_7162)
      | ~ v1_funct_1(B_7161)
      | ~ v1_relat_1(B_7161) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_231061,plain,(
    ! [B_7342,C_7343,A_7344] :
      ( k1_funct_1(k5_relat_1(B_7342,C_7343),A_7344) = k1_funct_1(C_7343,k1_funct_1(B_7342,A_7344))
      | ~ v1_funct_1(C_7343)
      | ~ v1_relat_1(C_7343)
      | ~ v1_funct_1(B_7342)
      | ~ v1_relat_1(B_7342)
      | v1_xboole_0(k1_relat_1(B_7342))
      | ~ m1_subset_1(A_7344,k1_relat_1(B_7342)) ) ),
    inference(resolution,[status(thm)],[c_10,c_227453])).

tff(c_231065,plain,(
    ! [C_7343,A_7344] :
      ( k1_funct_1(k5_relat_1('#skF_5',C_7343),A_7344) = k1_funct_1(C_7343,k1_funct_1('#skF_5',A_7344))
      | ~ v1_funct_1(C_7343)
      | ~ v1_relat_1(C_7343)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | v1_xboole_0(k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_7344,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4435,c_231061])).

tff(c_231075,plain,(
    ! [C_7343,A_7344] :
      ( k1_funct_1(k5_relat_1('#skF_5',C_7343),A_7344) = k1_funct_1(C_7343,k1_funct_1('#skF_5',A_7344))
      | ~ v1_funct_1(C_7343)
      | ~ v1_relat_1(C_7343)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_7344,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4435,c_119,c_66,c_231065])).

tff(c_237306,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_231075])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_237309,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_237306,c_2])).

tff(c_237313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_237309])).

tff(c_237314,plain,(
    ! [C_7343,A_7344] :
      ( k1_funct_1(k5_relat_1('#skF_5',C_7343),A_7344) = k1_funct_1(C_7343,k1_funct_1('#skF_5',A_7344))
      | ~ v1_funct_1(C_7343)
      | ~ v1_relat_1(C_7343)
      | ~ m1_subset_1(A_7344,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_231075])).

tff(c_4532,plain,(
    ! [B_377,C_378,A_379] :
      ( k1_funct_1(k5_relat_1(B_377,C_378),A_379) = k1_funct_1(C_378,k1_funct_1(B_377,A_379))
      | ~ r2_hidden(A_379,k1_relat_1(B_377))
      | ~ v1_funct_1(C_378)
      | ~ v1_relat_1(C_378)
      | ~ v1_funct_1(B_377)
      | ~ v1_relat_1(B_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_102356,plain,(
    ! [B_3541,C_3542,A_3543] :
      ( k1_funct_1(k5_relat_1(B_3541,C_3542),A_3543) = k1_funct_1(C_3542,k1_funct_1(B_3541,A_3543))
      | ~ v1_funct_1(C_3542)
      | ~ v1_relat_1(C_3542)
      | ~ v1_funct_1(B_3541)
      | ~ v1_relat_1(B_3541)
      | v1_xboole_0(k1_relat_1(B_3541))
      | ~ m1_subset_1(A_3543,k1_relat_1(B_3541)) ) ),
    inference(resolution,[status(thm)],[c_10,c_4532])).

tff(c_102358,plain,(
    ! [C_3542,A_3543] :
      ( k1_funct_1(k5_relat_1('#skF_5',C_3542),A_3543) = k1_funct_1(C_3542,k1_funct_1('#skF_5',A_3543))
      | ~ v1_funct_1(C_3542)
      | ~ v1_relat_1(C_3542)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | v1_xboole_0(k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_3543,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4435,c_102356])).

tff(c_102365,plain,(
    ! [C_3542,A_3543] :
      ( k1_funct_1(k5_relat_1('#skF_5',C_3542),A_3543) = k1_funct_1(C_3542,k1_funct_1('#skF_5',A_3543))
      | ~ v1_funct_1(C_3542)
      | ~ v1_relat_1(C_3542)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_3543,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4435,c_119,c_66,c_102358])).

tff(c_110403,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_102365])).

tff(c_110406,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_110403,c_2])).

tff(c_110410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_110406])).

tff(c_110411,plain,(
    ! [C_3542,A_3543] :
      ( k1_funct_1(k5_relat_1('#skF_5',C_3542),A_3543) = k1_funct_1(C_3542,k1_funct_1('#skF_5',A_3543))
      | ~ v1_funct_1(C_3542)
      | ~ v1_relat_1(C_3542)
      | ~ m1_subset_1(A_3543,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_102365])).

tff(c_8,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_77,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(A_66,B_67)
      | ~ m1_subset_1(A_66,k1_zfmisc_1(B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_97,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(resolution,[status(thm)],[c_8,c_77])).

tff(c_86243,plain,(
    ! [B_3053,C_3054,A_3055] :
      ( k1_funct_1(k5_relat_1(B_3053,C_3054),A_3055) = k1_funct_1(C_3054,k1_funct_1(B_3053,A_3055))
      | ~ v1_funct_1(C_3054)
      | ~ v1_relat_1(C_3054)
      | ~ v1_funct_1(B_3053)
      | ~ v1_relat_1(B_3053)
      | v1_xboole_0(k1_relat_1(B_3053))
      | ~ m1_subset_1(A_3055,k1_relat_1(B_3053)) ) ),
    inference(resolution,[status(thm)],[c_10,c_4532])).

tff(c_86247,plain,(
    ! [C_3054,A_3055] :
      ( k1_funct_1(k5_relat_1('#skF_5',C_3054),A_3055) = k1_funct_1(C_3054,k1_funct_1('#skF_5',A_3055))
      | ~ v1_funct_1(C_3054)
      | ~ v1_relat_1(C_3054)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | v1_xboole_0(k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_3055,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4435,c_86243])).

tff(c_86257,plain,(
    ! [C_3054,A_3055] :
      ( k1_funct_1(k5_relat_1('#skF_5',C_3054),A_3055) = k1_funct_1(C_3054,k1_funct_1('#skF_5',A_3055))
      | ~ v1_funct_1(C_3054)
      | ~ v1_relat_1(C_3054)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_3055,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4435,c_119,c_66,c_86247])).

tff(c_95739,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_86257])).

tff(c_95742,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_95739,c_2])).

tff(c_95746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_95742])).

tff(c_95747,plain,(
    ! [C_3054,A_3055] :
      ( k1_funct_1(k5_relat_1('#skF_5',C_3054),A_3055) = k1_funct_1(C_3054,k1_funct_1('#skF_5',A_3055))
      | ~ v1_funct_1(C_3054)
      | ~ v1_relat_1(C_3054)
      | ~ m1_subset_1(A_3055,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_86257])).

tff(c_4571,plain,(
    ! [E_381,B_386,C_383,D_384,F_385,A_382] :
      ( k1_partfun1(A_382,B_386,C_383,D_384,E_381,F_385) = k5_relat_1(E_381,F_385)
      | ~ m1_subset_1(F_385,k1_zfmisc_1(k2_zfmisc_1(C_383,D_384)))
      | ~ v1_funct_1(F_385)
      | ~ m1_subset_1(E_381,k1_zfmisc_1(k2_zfmisc_1(A_382,B_386)))
      | ~ v1_funct_1(E_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_4578,plain,(
    ! [A_382,B_386,E_381] :
      ( k1_partfun1(A_382,B_386,'#skF_4','#skF_2',E_381,'#skF_6') = k5_relat_1(E_381,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_381,k1_zfmisc_1(k2_zfmisc_1(A_382,B_386)))
      | ~ v1_funct_1(E_381) ) ),
    inference(resolution,[status(thm)],[c_58,c_4571])).

tff(c_84732,plain,(
    ! [A_2999,B_3000,E_3001] :
      ( k1_partfun1(A_2999,B_3000,'#skF_4','#skF_2',E_3001,'#skF_6') = k5_relat_1(E_3001,'#skF_6')
      | ~ m1_subset_1(E_3001,k1_zfmisc_1(k2_zfmisc_1(A_2999,B_3000)))
      | ~ v1_funct_1(E_3001) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_4578])).

tff(c_84739,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_84732])).

tff(c_84754,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_84739])).

tff(c_609,plain,(
    k1_relset_1('#skF_4','#skF_2','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_588])).

tff(c_54,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_617,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_609,c_54])).

tff(c_190,plain,(
    ! [C_83,A_84,B_85] :
      ( v4_relat_1(C_83,A_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_211,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_190])).

tff(c_95,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_62,c_77])).

tff(c_264,plain,(
    ! [A_97,C_98,B_99] :
      ( r1_tarski(A_97,C_98)
      | ~ r1_tarski(B_99,C_98)
      | ~ r1_tarski(A_97,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_276,plain,(
    ! [A_97] :
      ( r1_tarski(A_97,k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r1_tarski(A_97,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_95,c_264])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4477,plain,(
    ! [B_373,C_374,A_375] :
      ( k1_xboole_0 = B_373
      | v1_funct_2(C_374,A_375,B_373)
      | k1_relset_1(A_375,B_373,C_374) != A_375
      | ~ m1_subset_1(C_374,k1_zfmisc_1(k2_zfmisc_1(A_375,B_373))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_69050,plain,(
    ! [B_2489,A_2490,A_2491] :
      ( k1_xboole_0 = B_2489
      | v1_funct_2(A_2490,A_2491,B_2489)
      | k1_relset_1(A_2491,B_2489,A_2490) != A_2491
      | ~ r1_tarski(A_2490,k2_zfmisc_1(A_2491,B_2489)) ) ),
    inference(resolution,[status(thm)],[c_14,c_4477])).

tff(c_69110,plain,(
    ! [A_97] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2(A_97,'#skF_3','#skF_4')
      | k1_relset_1('#skF_3','#skF_4',A_97) != '#skF_3'
      | ~ r1_tarski(A_97,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_276,c_69050])).

tff(c_94836,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_69110])).

tff(c_334,plain,(
    ! [B_108,A_109] :
      ( r1_tarski(k1_relat_1(B_108),A_109)
      | ~ v4_relat_1(B_108,A_109)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [A_2,C_4,B_3] :
      ( r1_tarski(A_2,C_4)
      | ~ r1_tarski(B_3,C_4)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4970,plain,(
    ! [A_423,A_424,B_425] :
      ( r1_tarski(A_423,A_424)
      | ~ r1_tarski(A_423,k1_relat_1(B_425))
      | ~ v4_relat_1(B_425,A_424)
      | ~ v1_relat_1(B_425) ) ),
    inference(resolution,[status(thm)],[c_334,c_4])).

tff(c_4988,plain,(
    ! [A_424] :
      ( r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),A_424)
      | ~ v4_relat_1('#skF_6',A_424)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_617,c_4970])).

tff(c_5024,plain,(
    ! [A_426] :
      ( r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),A_426)
      | ~ v4_relat_1('#skF_6',A_426) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_4988])).

tff(c_278,plain,(
    ! [A_97,A_7] :
      ( r1_tarski(A_97,A_7)
      | ~ r1_tarski(A_97,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_97,c_264])).

tff(c_5093,plain,(
    ! [A_7] :
      ( r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),A_7)
      | ~ v4_relat_1('#skF_6',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_5024,c_278])).

tff(c_68123,plain,(
    ~ v4_relat_1('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_5093])).

tff(c_94860,plain,(
    ~ v4_relat_1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94836,c_68123])).

tff(c_94896,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_94860])).

tff(c_94898,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_69110])).

tff(c_4678,plain,(
    ! [A_397,C_396,B_395,D_398,E_394] :
      ( k1_partfun1(A_397,B_395,B_395,C_396,D_398,E_394) = k8_funct_2(A_397,B_395,C_396,D_398,E_394)
      | k1_xboole_0 = B_395
      | ~ r1_tarski(k2_relset_1(A_397,B_395,D_398),k1_relset_1(B_395,C_396,E_394))
      | ~ m1_subset_1(E_394,k1_zfmisc_1(k2_zfmisc_1(B_395,C_396)))
      | ~ v1_funct_1(E_394)
      | ~ m1_subset_1(D_398,k1_zfmisc_1(k2_zfmisc_1(A_397,B_395)))
      | ~ v1_funct_2(D_398,A_397,B_395)
      | ~ v1_funct_1(D_398) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4687,plain,(
    ! [A_397,D_398] :
      ( k1_partfun1(A_397,'#skF_4','#skF_4','#skF_2',D_398,'#skF_6') = k8_funct_2(A_397,'#skF_4','#skF_2',D_398,'#skF_6')
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relset_1(A_397,'#skF_4',D_398),k1_relat_1('#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(D_398,k1_zfmisc_1(k2_zfmisc_1(A_397,'#skF_4')))
      | ~ v1_funct_2(D_398,A_397,'#skF_4')
      | ~ v1_funct_1(D_398) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_609,c_4678])).

tff(c_4694,plain,(
    ! [A_397,D_398] :
      ( k1_partfun1(A_397,'#skF_4','#skF_4','#skF_2',D_398,'#skF_6') = k8_funct_2(A_397,'#skF_4','#skF_2',D_398,'#skF_6')
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relset_1(A_397,'#skF_4',D_398),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(D_398,k1_zfmisc_1(k2_zfmisc_1(A_397,'#skF_4')))
      | ~ v1_funct_2(D_398,A_397,'#skF_4')
      | ~ v1_funct_1(D_398) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_4687])).

tff(c_100447,plain,(
    ! [A_3433,D_3434] :
      ( k1_partfun1(A_3433,'#skF_4','#skF_4','#skF_2',D_3434,'#skF_6') = k8_funct_2(A_3433,'#skF_4','#skF_2',D_3434,'#skF_6')
      | ~ r1_tarski(k2_relset_1(A_3433,'#skF_4',D_3434),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(D_3434,k1_zfmisc_1(k2_zfmisc_1(A_3433,'#skF_4')))
      | ~ v1_funct_2(D_3434,A_3433,'#skF_4')
      | ~ v1_funct_1(D_3434) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94898,c_4694])).

tff(c_100454,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_617,c_100447])).

tff(c_100460,plain,(
    k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_84754,c_100454])).

tff(c_50,plain,(
    k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_100461,plain,(
    k1_funct_1(k5_relat_1('#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100460,c_50])).

tff(c_100468,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_95747,c_100461])).

tff(c_100475,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_120,c_60,c_100468])).

tff(c_100508,plain,(
    ! [A_3436] : r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),A_3436) ),
    inference(splitRight,[status(thm)],[c_5093])).

tff(c_126,plain,(
    ! [A_75,B_76] :
      ( r2_hidden(A_75,B_76)
      | v1_xboole_0(B_76)
      | ~ m1_subset_1(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    ! [B_22,A_21] :
      ( ~ r1_tarski(B_22,A_21)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_130,plain,(
    ! [B_76,A_75] :
      ( ~ r1_tarski(B_76,A_75)
      | v1_xboole_0(B_76)
      | ~ m1_subset_1(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_126,c_24])).

tff(c_100595,plain,(
    ! [A_3436] :
      ( v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(A_3436,k2_relset_1('#skF_3','#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_100508,c_130])).

tff(c_106975,plain,(
    ! [A_3658] : ~ m1_subset_1(A_3658,k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_100595])).

tff(c_106985,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_106975])).

tff(c_106986,plain,(
    v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_100595])).

tff(c_106990,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_106986,c_2])).

tff(c_101456,plain,(
    ! [A_3472,B_3473,E_3474] :
      ( k1_partfun1(A_3472,B_3473,'#skF_4','#skF_2',E_3474,'#skF_6') = k5_relat_1(E_3474,'#skF_6')
      | ~ m1_subset_1(E_3474,k1_zfmisc_1(k2_zfmisc_1(A_3472,B_3473)))
      | ~ v1_funct_1(E_3474) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_4578])).

tff(c_101463,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_101456])).

tff(c_101478,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_101463])).

tff(c_100477,plain,(
    v4_relat_1('#skF_6',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_5093])).

tff(c_4233,plain,(
    ! [B_358,A_359] :
      ( r1_tarski(k1_relat_1(B_358),A_359)
      | ~ v4_relat_1(B_358,k1_xboole_0)
      | ~ v1_relat_1(B_358) ) ),
    inference(resolution,[status(thm)],[c_334,c_278])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( v4_relat_1(B_16,A_15)
      | ~ r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4287,plain,(
    ! [B_358,A_359] :
      ( v4_relat_1(B_358,A_359)
      | ~ v4_relat_1(B_358,k1_xboole_0)
      | ~ v1_relat_1(B_358) ) ),
    inference(resolution,[status(thm)],[c_4233,c_18])).

tff(c_100479,plain,(
    ! [A_359] :
      ( v4_relat_1('#skF_6',A_359)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_100477,c_4287])).

tff(c_100482,plain,(
    ! [A_359] : v4_relat_1('#skF_6',A_359) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_100479])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_98,plain,(
    ! [B_67] : r1_tarski('#skF_1'(k1_zfmisc_1(B_67)),B_67) ),
    inference(resolution,[status(thm)],[c_6,c_77])).

tff(c_399,plain,(
    ! [A_114,B_115] :
      ( r1_tarski(A_114,B_115)
      | ~ r1_tarski(A_114,'#skF_1'(k1_zfmisc_1(B_115))) ) ),
    inference(resolution,[status(thm)],[c_98,c_264])).

tff(c_102985,plain,(
    ! [B_3591,B_3592] :
      ( r1_tarski(k1_relat_1(B_3591),B_3592)
      | ~ v4_relat_1(B_3591,'#skF_1'(k1_zfmisc_1(B_3592)))
      | ~ v1_relat_1(B_3591) ) ),
    inference(resolution,[status(thm)],[c_20,c_399])).

tff(c_103077,plain,(
    ! [B_3592] :
      ( r1_tarski(k1_relat_1('#skF_6'),B_3592)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_100482,c_102985])).

tff(c_103218,plain,(
    ! [B_3595] : r1_tarski(k1_relat_1('#skF_6'),B_3595) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_103077])).

tff(c_103348,plain,(
    ! [B_3595] :
      ( v1_xboole_0(k1_relat_1('#skF_6'))
      | ~ m1_subset_1(B_3595,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_103218,c_130])).

tff(c_103777,plain,(
    ! [B_3600] : ~ m1_subset_1(B_3600,k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_103348])).

tff(c_103787,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_103777])).

tff(c_103788,plain,(
    v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_103348])).

tff(c_103792,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_103788,c_2])).

tff(c_4368,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_4','#skF_2','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_4358])).

tff(c_4382,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_609,c_4368])).

tff(c_4436,plain,(
    ~ v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4382])).

tff(c_4487,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_6','#skF_4','#skF_2')
    | k1_relset_1('#skF_4','#skF_2','#skF_6') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_58,c_4477])).

tff(c_4501,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_6','#skF_4','#skF_2')
    | k1_relat_1('#skF_6') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_609,c_4487])).

tff(c_4502,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_6') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_4436,c_4501])).

tff(c_4506,plain,(
    k1_relat_1('#skF_6') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4502])).

tff(c_103820,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103792,c_4506])).

tff(c_113389,plain,(
    ! [A_397,D_398] :
      ( k1_partfun1(A_397,'#skF_4','#skF_4','#skF_2',D_398,'#skF_6') = k8_funct_2(A_397,'#skF_4','#skF_2',D_398,'#skF_6')
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relset_1(A_397,'#skF_4',D_398),k1_xboole_0)
      | ~ m1_subset_1(D_398,k1_zfmisc_1(k2_zfmisc_1(A_397,'#skF_4')))
      | ~ v1_funct_2(D_398,A_397,'#skF_4')
      | ~ v1_funct_1(D_398) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103792,c_4694])).

tff(c_113391,plain,(
    ! [A_3875,D_3876] :
      ( k1_partfun1(A_3875,'#skF_4','#skF_4','#skF_2',D_3876,'#skF_6') = k8_funct_2(A_3875,'#skF_4','#skF_2',D_3876,'#skF_6')
      | ~ r1_tarski(k2_relset_1(A_3875,'#skF_4',D_3876),k1_xboole_0)
      | ~ m1_subset_1(D_3876,k1_zfmisc_1(k2_zfmisc_1(A_3875,'#skF_4')))
      | ~ v1_funct_2(D_3876,A_3875,'#skF_4')
      | ~ v1_funct_1(D_3876) ) ),
    inference(negUnitSimplification,[status(thm)],[c_103820,c_113389])).

tff(c_113402,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_xboole_0)
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_113391])).

tff(c_113415,plain,(
    k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_97,c_106990,c_101478,c_113402])).

tff(c_113418,plain,(
    k1_funct_1(k5_relat_1('#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113415,c_50])).

tff(c_113425,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_110411,c_113418])).

tff(c_113432,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_120,c_60,c_113425])).

tff(c_113434,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4502])).

tff(c_113481,plain,(
    ! [A_15] :
      ( v4_relat_1('#skF_6',A_15)
      | ~ r1_tarski('#skF_4',A_15)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113434,c_18])).

tff(c_113491,plain,(
    ! [A_15] :
      ( v4_relat_1('#skF_6',A_15)
      | ~ r1_tarski('#skF_4',A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_113481])).

tff(c_113433,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4502])).

tff(c_143170,plain,(
    ! [B_4742,A_4743] :
      ( v4_relat_1(B_4742,A_4743)
      | ~ v4_relat_1(B_4742,'#skF_2')
      | ~ v1_relat_1(B_4742) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113433,c_4287])).

tff(c_143176,plain,(
    ! [A_4743] :
      ( v4_relat_1('#skF_6',A_4743)
      | ~ v1_relat_1('#skF_6')
      | ~ r1_tarski('#skF_4','#skF_2') ) ),
    inference(resolution,[status(thm)],[c_113491,c_143170])).

tff(c_143191,plain,(
    ! [A_4743] :
      ( v4_relat_1('#skF_6',A_4743)
      | ~ r1_tarski('#skF_4','#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_143176])).

tff(c_143201,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_143191])).

tff(c_113459,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113433,c_52])).

tff(c_113537,plain,(
    ! [B_3879,C_3880,A_3881] :
      ( k1_funct_1(k5_relat_1(B_3879,C_3880),A_3881) = k1_funct_1(C_3880,k1_funct_1(B_3879,A_3881))
      | ~ r2_hidden(A_3881,k1_relat_1(B_3879))
      | ~ v1_funct_1(C_3880)
      | ~ v1_relat_1(C_3880)
      | ~ v1_funct_1(B_3879)
      | ~ v1_relat_1(B_3879) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_147090,plain,(
    ! [B_4904,C_4905,A_4906] :
      ( k1_funct_1(k5_relat_1(B_4904,C_4905),A_4906) = k1_funct_1(C_4905,k1_funct_1(B_4904,A_4906))
      | ~ v1_funct_1(C_4905)
      | ~ v1_relat_1(C_4905)
      | ~ v1_funct_1(B_4904)
      | ~ v1_relat_1(B_4904)
      | v1_xboole_0(k1_relat_1(B_4904))
      | ~ m1_subset_1(A_4906,k1_relat_1(B_4904)) ) ),
    inference(resolution,[status(thm)],[c_10,c_113537])).

tff(c_147096,plain,(
    ! [C_4905,A_4906] :
      ( k1_funct_1(k5_relat_1('#skF_5',C_4905),A_4906) = k1_funct_1(C_4905,k1_funct_1('#skF_5',A_4906))
      | ~ v1_funct_1(C_4905)
      | ~ v1_relat_1(C_4905)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | v1_xboole_0(k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_4906,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4435,c_147090])).

tff(c_147106,plain,(
    ! [C_4905,A_4906] :
      ( k1_funct_1(k5_relat_1('#skF_5',C_4905),A_4906) = k1_funct_1(C_4905,k1_funct_1('#skF_5',A_4906))
      | ~ v1_funct_1(C_4905)
      | ~ v1_relat_1(C_4905)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_4906,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4435,c_119,c_66,c_147096])).

tff(c_163296,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_147106])).

tff(c_113457,plain,(
    ! [A_1] :
      ( A_1 = '#skF_2'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113433,c_2])).

tff(c_163299,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_163296,c_113457])).

tff(c_163303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_113459,c_163299])).

tff(c_163304,plain,(
    ! [C_4905,A_4906] :
      ( k1_funct_1(k5_relat_1('#skF_5',C_4905),A_4906) = k1_funct_1(C_4905,k1_funct_1('#skF_5',A_4906))
      | ~ v1_funct_1(C_4905)
      | ~ v1_relat_1(C_4905)
      | ~ m1_subset_1(A_4906,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_147106])).

tff(c_113467,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113434,c_617])).

tff(c_113620,plain,(
    ! [A_3886,B_3890,C_3887,E_3885,F_3889,D_3888] :
      ( k1_partfun1(A_3886,B_3890,C_3887,D_3888,E_3885,F_3889) = k5_relat_1(E_3885,F_3889)
      | ~ m1_subset_1(F_3889,k1_zfmisc_1(k2_zfmisc_1(C_3887,D_3888)))
      | ~ v1_funct_1(F_3889)
      | ~ m1_subset_1(E_3885,k1_zfmisc_1(k2_zfmisc_1(A_3886,B_3890)))
      | ~ v1_funct_1(E_3885) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_113630,plain,(
    ! [A_3886,B_3890,E_3885] :
      ( k1_partfun1(A_3886,B_3890,'#skF_4','#skF_2',E_3885,'#skF_6') = k5_relat_1(E_3885,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_3885,k1_zfmisc_1(k2_zfmisc_1(A_3886,B_3890)))
      | ~ v1_funct_1(E_3885) ) ),
    inference(resolution,[status(thm)],[c_58,c_113620])).

tff(c_144126,plain,(
    ! [A_4777,B_4778,E_4779] :
      ( k1_partfun1(A_4777,B_4778,'#skF_4','#skF_2',E_4779,'#skF_6') = k5_relat_1(E_4779,'#skF_6')
      | ~ m1_subset_1(E_4779,k1_zfmisc_1(k2_zfmisc_1(A_4777,B_4778)))
      | ~ v1_funct_1(E_4779) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_113630])).

tff(c_144137,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_144126])).

tff(c_144149,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_144137])).

tff(c_96,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_77])).

tff(c_277,plain,(
    ! [A_97] :
      ( r1_tarski(A_97,k2_zfmisc_1('#skF_4','#skF_2'))
      | ~ r1_tarski(A_97,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_96,c_264])).

tff(c_702,plain,(
    ! [C_141,A_142] :
      ( k1_xboole_0 = C_141
      | ~ v1_funct_2(C_141,A_142,k1_xboole_0)
      | k1_xboole_0 = A_142
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_142,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_715,plain,(
    ! [A_10,A_142] :
      ( k1_xboole_0 = A_10
      | ~ v1_funct_2(A_10,A_142,k1_xboole_0)
      | k1_xboole_0 = A_142
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_142,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_14,c_702])).

tff(c_143364,plain,(
    ! [A_4755,A_4756] :
      ( A_4755 = '#skF_2'
      | ~ v1_funct_2(A_4755,A_4756,'#skF_2')
      | A_4756 = '#skF_2'
      | ~ r1_tarski(A_4755,k2_zfmisc_1(A_4756,'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113433,c_113433,c_113433,c_113433,c_715])).

tff(c_143388,plain,(
    ! [A_97] :
      ( A_97 = '#skF_2'
      | ~ v1_funct_2(A_97,'#skF_4','#skF_2')
      | '#skF_2' = '#skF_4'
      | ~ r1_tarski(A_97,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_277,c_143364])).

tff(c_148124,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_143388])).

tff(c_143202,plain,(
    ! [A_4744,A_4745,B_4746] :
      ( r1_tarski(A_4744,A_4745)
      | ~ r1_tarski(A_4744,k1_relat_1(B_4746))
      | ~ v4_relat_1(B_4746,A_4745)
      | ~ v1_relat_1(B_4746) ) ),
    inference(resolution,[status(thm)],[c_334,c_4])).

tff(c_143209,plain,(
    ! [A_4744,A_4745] :
      ( r1_tarski(A_4744,A_4745)
      | ~ r1_tarski(A_4744,'#skF_4')
      | ~ v4_relat_1('#skF_6',A_4745)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113434,c_143202])).

tff(c_143393,plain,(
    ! [A_4757,A_4758] :
      ( r1_tarski(A_4757,A_4758)
      | ~ r1_tarski(A_4757,'#skF_4')
      | ~ v4_relat_1('#skF_6',A_4758) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_143209])).

tff(c_143426,plain,(
    ! [A_4759] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1('#skF_4')),A_4759)
      | ~ v4_relat_1('#skF_6',A_4759) ) ),
    inference(resolution,[status(thm)],[c_98,c_143393])).

tff(c_113450,plain,(
    ! [A_97,A_7] :
      ( r1_tarski(A_97,A_7)
      | ~ r1_tarski(A_97,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113433,c_278])).

tff(c_143499,plain,(
    ! [A_7] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1('#skF_4')),A_7)
      | ~ v4_relat_1('#skF_6','#skF_2') ) ),
    inference(resolution,[status(thm)],[c_143426,c_113450])).

tff(c_143516,plain,(
    ~ v4_relat_1('#skF_6','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_143499])).

tff(c_148194,plain,(
    ~ v4_relat_1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148124,c_143516])).

tff(c_148235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_148194])).

tff(c_148237,plain,(
    '#skF_2' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_143388])).

tff(c_113468,plain,(
    k1_relset_1('#skF_4','#skF_2','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113434,c_609])).

tff(c_34,plain,(
    ! [B_33,C_34,E_37,A_32,D_35] :
      ( k1_partfun1(A_32,B_33,B_33,C_34,D_35,E_37) = k8_funct_2(A_32,B_33,C_34,D_35,E_37)
      | k1_xboole_0 = B_33
      | ~ r1_tarski(k2_relset_1(A_32,B_33,D_35),k1_relset_1(B_33,C_34,E_37))
      | ~ m1_subset_1(E_37,k1_zfmisc_1(k2_zfmisc_1(B_33,C_34)))
      | ~ v1_funct_1(E_37)
      | ~ m1_subset_1(D_35,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_2(D_35,A_32,B_33)
      | ~ v1_funct_1(D_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_113693,plain,(
    ! [A_3897,E_3894,D_3898,C_3896,B_3895] :
      ( k1_partfun1(A_3897,B_3895,B_3895,C_3896,D_3898,E_3894) = k8_funct_2(A_3897,B_3895,C_3896,D_3898,E_3894)
      | B_3895 = '#skF_2'
      | ~ r1_tarski(k2_relset_1(A_3897,B_3895,D_3898),k1_relset_1(B_3895,C_3896,E_3894))
      | ~ m1_subset_1(E_3894,k1_zfmisc_1(k2_zfmisc_1(B_3895,C_3896)))
      | ~ v1_funct_1(E_3894)
      | ~ m1_subset_1(D_3898,k1_zfmisc_1(k2_zfmisc_1(A_3897,B_3895)))
      | ~ v1_funct_2(D_3898,A_3897,B_3895)
      | ~ v1_funct_1(D_3898) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113433,c_34])).

tff(c_113699,plain,(
    ! [A_3897,D_3898] :
      ( k1_partfun1(A_3897,'#skF_4','#skF_4','#skF_2',D_3898,'#skF_6') = k8_funct_2(A_3897,'#skF_4','#skF_2',D_3898,'#skF_6')
      | '#skF_2' = '#skF_4'
      | ~ r1_tarski(k2_relset_1(A_3897,'#skF_4',D_3898),'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(D_3898,k1_zfmisc_1(k2_zfmisc_1(A_3897,'#skF_4')))
      | ~ v1_funct_2(D_3898,A_3897,'#skF_4')
      | ~ v1_funct_1(D_3898) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113468,c_113693])).

tff(c_113706,plain,(
    ! [A_3897,D_3898] :
      ( k1_partfun1(A_3897,'#skF_4','#skF_4','#skF_2',D_3898,'#skF_6') = k8_funct_2(A_3897,'#skF_4','#skF_2',D_3898,'#skF_6')
      | '#skF_2' = '#skF_4'
      | ~ r1_tarski(k2_relset_1(A_3897,'#skF_4',D_3898),'#skF_4')
      | ~ m1_subset_1(D_3898,k1_zfmisc_1(k2_zfmisc_1(A_3897,'#skF_4')))
      | ~ v1_funct_2(D_3898,A_3897,'#skF_4')
      | ~ v1_funct_1(D_3898) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_113699])).

tff(c_168508,plain,(
    ! [A_5403,D_5404] :
      ( k1_partfun1(A_5403,'#skF_4','#skF_4','#skF_2',D_5404,'#skF_6') = k8_funct_2(A_5403,'#skF_4','#skF_2',D_5404,'#skF_6')
      | ~ r1_tarski(k2_relset_1(A_5403,'#skF_4',D_5404),'#skF_4')
      | ~ m1_subset_1(D_5404,k1_zfmisc_1(k2_zfmisc_1(A_5403,'#skF_4')))
      | ~ v1_funct_2(D_5404,A_5403,'#skF_4')
      | ~ v1_funct_1(D_5404) ) ),
    inference(negUnitSimplification,[status(thm)],[c_148237,c_113706])).

tff(c_168523,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_168508])).

tff(c_168533,plain,(
    k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_113467,c_144149,c_168523])).

tff(c_168535,plain,(
    k1_funct_1(k5_relat_1('#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168533,c_50])).

tff(c_168542,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_163304,c_168535])).

tff(c_168549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_120,c_60,c_168542])).

tff(c_168551,plain,(
    v4_relat_1('#skF_6','#skF_2') ),
    inference(splitRight,[status(thm)],[c_143499])).

tff(c_113478,plain,(
    ! [A_15] :
      ( r1_tarski('#skF_4',A_15)
      | ~ v4_relat_1('#skF_6',A_15)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113434,c_20])).

tff(c_113489,plain,(
    ! [A_15] :
      ( r1_tarski('#skF_4',A_15)
      | ~ v4_relat_1('#skF_6',A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_113478])).

tff(c_168556,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_168551,c_113489])).

tff(c_168563,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143201,c_168556])).

tff(c_168564,plain,(
    ! [A_4743] : v4_relat_1('#skF_6',A_4743) ),
    inference(splitRight,[status(thm)],[c_143191])).

tff(c_168628,plain,(
    ! [A_5409] : r1_tarski('#skF_4',A_5409) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168564,c_113489])).

tff(c_168668,plain,(
    ! [A_5409] :
      ( v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_5409,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_168628,c_130])).

tff(c_168731,plain,(
    ! [A_5414] : ~ m1_subset_1(A_5414,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_168668])).

tff(c_168736,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_168731])).

tff(c_168737,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4382])).

tff(c_168778,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_168737])).

tff(c_121,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_99])).

tff(c_168797,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168778,c_121])).

tff(c_168738,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_4382])).

tff(c_170072,plain,(
    ! [A_5485,A_5486] :
      ( A_5485 = '#skF_2'
      | ~ v1_funct_2(A_5485,A_5486,'#skF_2')
      | A_5486 = '#skF_2'
      | ~ r1_tarski(A_5485,k2_zfmisc_1(A_5486,'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168778,c_168778,c_168778,c_168778,c_715])).

tff(c_170106,plain,
    ( '#skF_6' = '#skF_2'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_2')
    | '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_96,c_170072])).

tff(c_170117,plain,
    ( '#skF_6' = '#skF_2'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168738,c_170106])).

tff(c_170118,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_170117])).

tff(c_154,plain,(
    ! [B_80,A_81] :
      ( ~ r1_tarski(B_80,A_81)
      | v1_xboole_0(B_80)
      | ~ m1_subset_1(A_81,B_80) ) ),
    inference(resolution,[status(thm)],[c_126,c_24])).

tff(c_173,plain,(
    ! [A_7] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_7,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_97,c_154])).

tff(c_176,plain,(
    ! [A_82] : ~ m1_subset_1(A_82,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_181,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_176])).

tff(c_182,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_168795,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168778,c_182])).

tff(c_170141,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170118,c_168795])).

tff(c_170157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_170141])).

tff(c_170158,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_170117])).

tff(c_170195,plain,(
    v1_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170158,c_60])).

tff(c_168801,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168778,c_52])).

tff(c_168952,plain,(
    ! [B_5423,C_5424,A_5425] :
      ( k1_funct_1(k5_relat_1(B_5423,C_5424),A_5425) = k1_funct_1(C_5424,k1_funct_1(B_5423,A_5425))
      | ~ r2_hidden(A_5425,k1_relat_1(B_5423))
      | ~ v1_funct_1(C_5424)
      | ~ v1_relat_1(C_5424)
      | ~ v1_funct_1(B_5423)
      | ~ v1_relat_1(B_5423) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_172403,plain,(
    ! [B_5620,C_5621,A_5622] :
      ( k1_funct_1(k5_relat_1(B_5620,C_5621),A_5622) = k1_funct_1(C_5621,k1_funct_1(B_5620,A_5622))
      | ~ v1_funct_1(C_5621)
      | ~ v1_relat_1(C_5621)
      | ~ v1_funct_1(B_5620)
      | ~ v1_relat_1(B_5620)
      | v1_xboole_0(k1_relat_1(B_5620))
      | ~ m1_subset_1(A_5622,k1_relat_1(B_5620)) ) ),
    inference(resolution,[status(thm)],[c_10,c_168952])).

tff(c_172407,plain,(
    ! [C_5621,A_5622] :
      ( k1_funct_1(k5_relat_1('#skF_5',C_5621),A_5622) = k1_funct_1(C_5621,k1_funct_1('#skF_5',A_5622))
      | ~ v1_funct_1(C_5621)
      | ~ v1_relat_1(C_5621)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | v1_xboole_0(k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_5622,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4435,c_172403])).

tff(c_172414,plain,(
    ! [C_5621,A_5622] :
      ( k1_funct_1(k5_relat_1('#skF_5',C_5621),A_5622) = k1_funct_1(C_5621,k1_funct_1('#skF_5',A_5622))
      | ~ v1_funct_1(C_5621)
      | ~ v1_relat_1(C_5621)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_5622,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4435,c_119,c_66,c_172407])).

tff(c_178505,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_172414])).

tff(c_168799,plain,(
    ! [A_1] :
      ( A_1 = '#skF_2'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168778,c_2])).

tff(c_178508,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_178505,c_168799])).

tff(c_178512,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_168801,c_178508])).

tff(c_178513,plain,(
    ! [C_5621,A_5622] :
      ( k1_funct_1(k5_relat_1('#skF_5',C_5621),A_5622) = k1_funct_1(C_5621,k1_funct_1('#skF_5',A_5622))
      | ~ v1_funct_1(C_5621)
      | ~ v1_relat_1(C_5621)
      | ~ m1_subset_1(A_5622,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_172414])).

tff(c_168796,plain,(
    ! [A_7] : r1_tarski('#skF_2',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168778,c_97])).

tff(c_212,plain,(
    ! [A_84] : v4_relat_1(k1_xboole_0,A_84) ),
    inference(resolution,[status(thm)],[c_8,c_190])).

tff(c_168794,plain,(
    ! [A_84] : v4_relat_1('#skF_2',A_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168778,c_212])).

tff(c_169458,plain,(
    ! [A_5466,A_5467,B_5468] :
      ( r1_tarski(A_5466,A_5467)
      | ~ r1_tarski(A_5466,k1_relat_1(B_5468))
      | ~ v4_relat_1(B_5468,A_5467)
      | ~ v1_relat_1(B_5468) ) ),
    inference(resolution,[status(thm)],[c_334,c_4])).

tff(c_169479,plain,(
    ! [A_5467] :
      ( r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),A_5467)
      | ~ v4_relat_1('#skF_6',A_5467)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_617,c_169458])).

tff(c_169508,plain,(
    ! [A_5467] :
      ( r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),A_5467)
      | ~ v4_relat_1('#skF_6',A_5467) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_169479])).

tff(c_170166,plain,(
    ! [A_5467] :
      ( r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),A_5467)
      | ~ v4_relat_1('#skF_2',A_5467) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170158,c_169508])).

tff(c_170310,plain,(
    ! [A_5490] : r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),A_5490) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168794,c_170166])).

tff(c_170392,plain,(
    ! [A_5490] :
      ( v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(A_5490,k2_relset_1('#skF_3','#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_170310,c_130])).

tff(c_175814,plain,(
    ! [A_5713] : ~ m1_subset_1(A_5713,k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_170392])).

tff(c_175824,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_175814])).

tff(c_175825,plain,(
    v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_170392])).

tff(c_175829,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_175825,c_168799])).

tff(c_169003,plain,(
    ! [C_5431,D_5432,A_5430,F_5433,E_5429,B_5434] :
      ( k1_partfun1(A_5430,B_5434,C_5431,D_5432,E_5429,F_5433) = k5_relat_1(E_5429,F_5433)
      | ~ m1_subset_1(F_5433,k1_zfmisc_1(k2_zfmisc_1(C_5431,D_5432)))
      | ~ v1_funct_1(F_5433)
      | ~ m1_subset_1(E_5429,k1_zfmisc_1(k2_zfmisc_1(A_5430,B_5434)))
      | ~ v1_funct_1(E_5429) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_172228,plain,(
    ! [A_5609,E_5608,D_5606,A_5607,B_5605,C_5604] :
      ( k1_partfun1(A_5607,B_5605,C_5604,D_5606,E_5608,A_5609) = k5_relat_1(E_5608,A_5609)
      | ~ v1_funct_1(A_5609)
      | ~ m1_subset_1(E_5608,k1_zfmisc_1(k2_zfmisc_1(A_5607,B_5605)))
      | ~ v1_funct_1(E_5608)
      | ~ r1_tarski(A_5609,k2_zfmisc_1(C_5604,D_5606)) ) ),
    inference(resolution,[status(thm)],[c_14,c_169003])).

tff(c_172236,plain,(
    ! [C_5604,D_5606,A_5609] :
      ( k1_partfun1('#skF_3','#skF_4',C_5604,D_5606,'#skF_5',A_5609) = k5_relat_1('#skF_5',A_5609)
      | ~ v1_funct_1(A_5609)
      | ~ v1_funct_1('#skF_5')
      | ~ r1_tarski(A_5609,k2_zfmisc_1(C_5604,D_5606)) ) ),
    inference(resolution,[status(thm)],[c_62,c_172228])).

tff(c_172269,plain,(
    ! [C_5612,D_5613,A_5614] :
      ( k1_partfun1('#skF_3','#skF_4',C_5612,D_5613,'#skF_5',A_5614) = k5_relat_1('#skF_5',A_5614)
      | ~ v1_funct_1(A_5614)
      | ~ r1_tarski(A_5614,k2_zfmisc_1(C_5612,D_5613)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_172236])).

tff(c_172315,plain,(
    ! [C_5612,D_5613] :
      ( k1_partfun1('#skF_3','#skF_4',C_5612,D_5613,'#skF_5','#skF_2') = k5_relat_1('#skF_5','#skF_2')
      | ~ v1_funct_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_168796,c_172269])).

tff(c_172347,plain,(
    ! [C_5612,D_5613] : k1_partfun1('#skF_3','#skF_4',C_5612,D_5613,'#skF_5','#skF_2') = k5_relat_1('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170195,c_172315])).

tff(c_170159,plain,(
    '#skF_2' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_170117])).

tff(c_610,plain,(
    ! [A_131,B_132] : k1_relset_1(A_131,B_132,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_588])).

tff(c_758,plain,(
    ! [C_154,B_155] :
      ( v1_funct_2(C_154,k1_xboole_0,B_155)
      | k1_relset_1(k1_xboole_0,B_155,C_154) != k1_xboole_0
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_766,plain,(
    ! [B_155] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_155)
      | k1_relset_1(k1_xboole_0,B_155,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_758])).

tff(c_773,plain,(
    ! [B_155] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_155)
      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_766])).

tff(c_775,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_773])).

tff(c_3429,plain,(
    ! [B_338,B_339] :
      ( r1_tarski(k1_relat_1(B_338),B_339)
      | ~ v4_relat_1(B_338,'#skF_1'(k1_zfmisc_1(B_339)))
      | ~ v1_relat_1(B_338) ) ),
    inference(resolution,[status(thm)],[c_20,c_399])).

tff(c_3512,plain,(
    ! [B_339] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),B_339)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_212,c_3429])).

tff(c_3571,plain,(
    ! [B_340] : r1_tarski(k1_relat_1(k1_xboole_0),B_340) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_3512])).

tff(c_3688,plain,(
    ! [B_340] :
      ( v1_xboole_0(k1_relat_1(k1_xboole_0))
      | ~ m1_subset_1(B_340,k1_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_3571,c_130])).

tff(c_4143,plain,(
    ! [B_353] : ~ m1_subset_1(B_353,k1_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_3688])).

tff(c_4148,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_4143])).

tff(c_4149,plain,(
    v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_3688])).

tff(c_4152,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4149,c_2])).

tff(c_4156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_775,c_4152])).

tff(c_4158,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_773])).

tff(c_168788,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168778,c_168778,c_4158])).

tff(c_169056,plain,(
    ! [E_5439,D_5443,C_5441,B_5440,A_5442] :
      ( k1_partfun1(A_5442,B_5440,B_5440,C_5441,D_5443,E_5439) = k8_funct_2(A_5442,B_5440,C_5441,D_5443,E_5439)
      | B_5440 = '#skF_2'
      | ~ r1_tarski(k2_relset_1(A_5442,B_5440,D_5443),k1_relset_1(B_5440,C_5441,E_5439))
      | ~ m1_subset_1(E_5439,k1_zfmisc_1(k2_zfmisc_1(B_5440,C_5441)))
      | ~ v1_funct_1(E_5439)
      | ~ m1_subset_1(D_5443,k1_zfmisc_1(k2_zfmisc_1(A_5442,B_5440)))
      | ~ v1_funct_2(D_5443,A_5442,B_5440)
      | ~ v1_funct_1(D_5443) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168778,c_34])).

tff(c_169065,plain,(
    ! [A_5442,D_5443] :
      ( k1_partfun1(A_5442,'#skF_4','#skF_4','#skF_2',D_5443,'#skF_6') = k8_funct_2(A_5442,'#skF_4','#skF_2',D_5443,'#skF_6')
      | '#skF_2' = '#skF_4'
      | ~ r1_tarski(k2_relset_1(A_5442,'#skF_4',D_5443),k1_relat_1('#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(D_5443,k1_zfmisc_1(k2_zfmisc_1(A_5442,'#skF_4')))
      | ~ v1_funct_2(D_5443,A_5442,'#skF_4')
      | ~ v1_funct_1(D_5443) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_609,c_169056])).

tff(c_169072,plain,(
    ! [A_5442,D_5443] :
      ( k1_partfun1(A_5442,'#skF_4','#skF_4','#skF_2',D_5443,'#skF_6') = k8_funct_2(A_5442,'#skF_4','#skF_2',D_5443,'#skF_6')
      | '#skF_2' = '#skF_4'
      | ~ r1_tarski(k2_relset_1(A_5442,'#skF_4',D_5443),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(D_5443,k1_zfmisc_1(k2_zfmisc_1(A_5442,'#skF_4')))
      | ~ v1_funct_2(D_5443,A_5442,'#skF_4')
      | ~ v1_funct_1(D_5443) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_169065])).

tff(c_181961,plain,(
    ! [A_5442,D_5443] :
      ( k1_partfun1(A_5442,'#skF_4','#skF_4','#skF_2',D_5443,'#skF_2') = k8_funct_2(A_5442,'#skF_4','#skF_2',D_5443,'#skF_2')
      | '#skF_2' = '#skF_4'
      | ~ r1_tarski(k2_relset_1(A_5442,'#skF_4',D_5443),'#skF_2')
      | ~ m1_subset_1(D_5443,k1_zfmisc_1(k2_zfmisc_1(A_5442,'#skF_4')))
      | ~ v1_funct_2(D_5443,A_5442,'#skF_4')
      | ~ v1_funct_1(D_5443) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168788,c_170158,c_170158,c_170158,c_169072])).

tff(c_181963,plain,(
    ! [A_5928,D_5929] :
      ( k1_partfun1(A_5928,'#skF_4','#skF_4','#skF_2',D_5929,'#skF_2') = k8_funct_2(A_5928,'#skF_4','#skF_2',D_5929,'#skF_2')
      | ~ r1_tarski(k2_relset_1(A_5928,'#skF_4',D_5929),'#skF_2')
      | ~ m1_subset_1(D_5929,k1_zfmisc_1(k2_zfmisc_1(A_5928,'#skF_4')))
      | ~ v1_funct_2(D_5929,A_5928,'#skF_4')
      | ~ v1_funct_1(D_5929) ) ),
    inference(negUnitSimplification,[status(thm)],[c_170159,c_181961])).

tff(c_181978,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_2') = k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_2')
    | ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_2')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_181963])).

tff(c_181990,plain,(
    k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_2') = k5_relat_1('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_168796,c_175829,c_172347,c_181978])).

tff(c_170190,plain,(
    k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_2'),'#skF_7') != k1_funct_1('#skF_2',k1_funct_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170158,c_170158,c_50])).

tff(c_181992,plain,(
    k1_funct_1(k5_relat_1('#skF_5','#skF_2'),'#skF_7') != k1_funct_1('#skF_2',k1_funct_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181990,c_170190])).

tff(c_181999,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_178513,c_181992])).

tff(c_182006,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_168797,c_170195,c_181999])).

tff(c_182007,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_168737])).

tff(c_182013,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182007,c_617])).

tff(c_227543,plain,(
    ! [A_7168,B_7172,E_7167,F_7171,D_7170,C_7169] :
      ( k1_partfun1(A_7168,B_7172,C_7169,D_7170,E_7167,F_7171) = k5_relat_1(E_7167,F_7171)
      | ~ m1_subset_1(F_7171,k1_zfmisc_1(k2_zfmisc_1(C_7169,D_7170)))
      | ~ v1_funct_1(F_7171)
      | ~ m1_subset_1(E_7167,k1_zfmisc_1(k2_zfmisc_1(A_7168,B_7172)))
      | ~ v1_funct_1(E_7167) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_227550,plain,(
    ! [A_7168,B_7172,E_7167] :
      ( k1_partfun1(A_7168,B_7172,'#skF_4','#skF_2',E_7167,'#skF_6') = k5_relat_1(E_7167,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_7167,k1_zfmisc_1(k2_zfmisc_1(A_7168,B_7172)))
      | ~ v1_funct_1(E_7167) ) ),
    inference(resolution,[status(thm)],[c_58,c_227543])).

tff(c_228124,plain,(
    ! [A_7202,B_7203,E_7204] :
      ( k1_partfun1(A_7202,B_7203,'#skF_4','#skF_2',E_7204,'#skF_6') = k5_relat_1(E_7204,'#skF_6')
      | ~ m1_subset_1(E_7204,k1_zfmisc_1(k2_zfmisc_1(A_7202,B_7203)))
      | ~ v1_funct_1(E_7204) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_227550])).

tff(c_228131,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_228124])).

tff(c_228146,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_228131])).

tff(c_182030,plain,(
    ! [A_15] :
      ( r1_tarski('#skF_4',A_15)
      | ~ v4_relat_1('#skF_6',A_15)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182007,c_20])).

tff(c_227478,plain,(
    ! [A_7165] :
      ( r1_tarski('#skF_4',A_7165)
      | ~ v4_relat_1('#skF_6',A_7165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_182030])).

tff(c_227500,plain,(
    r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_211,c_227478])).

tff(c_182055,plain,(
    ! [B_5930,C_5931,A_5932] :
      ( k1_xboole_0 = B_5930
      | v1_funct_2(C_5931,A_5932,B_5930)
      | k1_relset_1(A_5932,B_5930,C_5931) != A_5932
      | ~ m1_subset_1(C_5931,k1_zfmisc_1(k2_zfmisc_1(A_5932,B_5930))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_229248,plain,(
    ! [B_7253,A_7254,A_7255] :
      ( k1_xboole_0 = B_7253
      | v1_funct_2(A_7254,A_7255,B_7253)
      | k1_relset_1(A_7255,B_7253,A_7254) != A_7255
      | ~ r1_tarski(A_7254,k2_zfmisc_1(A_7255,B_7253)) ) ),
    inference(resolution,[status(thm)],[c_14,c_182055])).

tff(c_229305,plain,(
    ! [A_97] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2(A_97,'#skF_3','#skF_4')
      | k1_relset_1('#skF_3','#skF_4',A_97) != '#skF_3'
      | ~ r1_tarski(A_97,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_276,c_229248])).

tff(c_237317,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_229305])).

tff(c_182033,plain,(
    ! [A_15] :
      ( v4_relat_1('#skF_6',A_15)
      | ~ r1_tarski('#skF_4',A_15)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182007,c_18])).

tff(c_182047,plain,(
    ! [A_15] :
      ( v4_relat_1('#skF_6',A_15)
      | ~ r1_tarski('#skF_4',A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_182033])).

tff(c_358,plain,(
    ! [B_108,A_7] :
      ( r1_tarski(k1_relat_1(B_108),A_7)
      | ~ v4_relat_1(B_108,k1_xboole_0)
      | ~ v1_relat_1(B_108) ) ),
    inference(resolution,[status(thm)],[c_334,c_278])).

tff(c_182021,plain,(
    ! [A_7] :
      ( r1_tarski('#skF_4',A_7)
      | ~ v4_relat_1('#skF_6',k1_xboole_0)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182007,c_358])).

tff(c_182039,plain,(
    ! [A_7] :
      ( r1_tarski('#skF_4',A_7)
      | ~ v4_relat_1('#skF_6',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_182021])).

tff(c_227630,plain,(
    ~ v4_relat_1('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_182039])).

tff(c_227634,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_182047,c_227630])).

tff(c_237348,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_237317,c_227634])).

tff(c_237380,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_227500,c_237348])).

tff(c_237382,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_229305])).

tff(c_182014,plain,(
    k1_relset_1('#skF_4','#skF_2','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_182007,c_609])).

tff(c_227594,plain,(
    ! [D_7178,A_7177,B_7175,E_7174,C_7176] :
      ( k1_partfun1(A_7177,B_7175,B_7175,C_7176,D_7178,E_7174) = k8_funct_2(A_7177,B_7175,C_7176,D_7178,E_7174)
      | k1_xboole_0 = B_7175
      | ~ r1_tarski(k2_relset_1(A_7177,B_7175,D_7178),k1_relset_1(B_7175,C_7176,E_7174))
      | ~ m1_subset_1(E_7174,k1_zfmisc_1(k2_zfmisc_1(B_7175,C_7176)))
      | ~ v1_funct_1(E_7174)
      | ~ m1_subset_1(D_7178,k1_zfmisc_1(k2_zfmisc_1(A_7177,B_7175)))
      | ~ v1_funct_2(D_7178,A_7177,B_7175)
      | ~ v1_funct_1(D_7178) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_227597,plain,(
    ! [A_7177,D_7178] :
      ( k1_partfun1(A_7177,'#skF_4','#skF_4','#skF_2',D_7178,'#skF_6') = k8_funct_2(A_7177,'#skF_4','#skF_2',D_7178,'#skF_6')
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relset_1(A_7177,'#skF_4',D_7178),'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(D_7178,k1_zfmisc_1(k2_zfmisc_1(A_7177,'#skF_4')))
      | ~ v1_funct_2(D_7178,A_7177,'#skF_4')
      | ~ v1_funct_1(D_7178) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182014,c_227594])).

tff(c_227605,plain,(
    ! [A_7177,D_7178] :
      ( k1_partfun1(A_7177,'#skF_4','#skF_4','#skF_2',D_7178,'#skF_6') = k8_funct_2(A_7177,'#skF_4','#skF_2',D_7178,'#skF_6')
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relset_1(A_7177,'#skF_4',D_7178),'#skF_4')
      | ~ m1_subset_1(D_7178,k1_zfmisc_1(k2_zfmisc_1(A_7177,'#skF_4')))
      | ~ v1_funct_2(D_7178,A_7177,'#skF_4')
      | ~ v1_funct_1(D_7178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_227597])).

tff(c_244282,plain,(
    ! [A_7685,D_7686] :
      ( k1_partfun1(A_7685,'#skF_4','#skF_4','#skF_2',D_7686,'#skF_6') = k8_funct_2(A_7685,'#skF_4','#skF_2',D_7686,'#skF_6')
      | ~ r1_tarski(k2_relset_1(A_7685,'#skF_4',D_7686),'#skF_4')
      | ~ m1_subset_1(D_7686,k1_zfmisc_1(k2_zfmisc_1(A_7685,'#skF_4')))
      | ~ v1_funct_2(D_7686,A_7685,'#skF_4')
      | ~ v1_funct_1(D_7686) ) ),
    inference(negUnitSimplification,[status(thm)],[c_237382,c_227605])).

tff(c_244293,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_244282])).

tff(c_244306,plain,(
    k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_182013,c_228146,c_244293])).

tff(c_244321,plain,(
    k1_funct_1(k5_relat_1('#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244306,c_50])).

tff(c_244424,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_237314,c_244321])).

tff(c_244431,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_120,c_60,c_244424])).

tff(c_244439,plain,(
    ! [A_7688] : r1_tarski('#skF_4',A_7688) ),
    inference(splitRight,[status(thm)],[c_182039])).

tff(c_244467,plain,(
    ! [A_7688] :
      ( v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_7688,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_244439,c_130])).

tff(c_244488,plain,(
    ! [A_7689] : ~ m1_subset_1(A_7689,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_244467])).

tff(c_244493,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_244488])).

tff(c_244494,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4380])).

tff(c_244512,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_244494,c_182])).

tff(c_244520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_244512])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 15:31:50 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 49.68/38.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 49.73/38.43  
% 49.73/38.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 49.73/38.43  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 49.73/38.43  
% 49.73/38.43  %Foreground sorts:
% 49.73/38.43  
% 49.73/38.43  
% 49.73/38.43  %Background operators:
% 49.73/38.43  
% 49.73/38.43  
% 49.73/38.43  %Foreground operators:
% 49.73/38.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 49.73/38.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 49.73/38.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 49.73/38.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 49.73/38.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 49.73/38.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 49.73/38.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 49.73/38.43  tff('#skF_7', type, '#skF_7': $i).
% 49.73/38.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 49.73/38.43  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 49.73/38.43  tff('#skF_5', type, '#skF_5': $i).
% 49.73/38.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 49.73/38.43  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 49.73/38.43  tff('#skF_6', type, '#skF_6': $i).
% 49.73/38.43  tff('#skF_2', type, '#skF_2': $i).
% 49.73/38.43  tff('#skF_3', type, '#skF_3': $i).
% 49.73/38.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 49.73/38.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 49.73/38.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 49.73/38.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 49.73/38.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 49.73/38.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 49.73/38.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 49.73/38.43  tff('#skF_4', type, '#skF_4': $i).
% 49.73/38.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 49.73/38.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 49.73/38.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 49.73/38.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 49.73/38.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 49.73/38.43  
% 50.04/38.48  tff(f_164, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 50.04/38.48  tff(f_38, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 50.04/38.48  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 50.04/38.48  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 50.04/38.48  tff(f_129, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 50.04/38.48  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 50.04/38.48  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 50.04/38.48  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 50.04/38.48  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 50.04/38.48  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 50.04/38.48  tff(f_139, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 50.04/38.48  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 50.04/38.48  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 50.04/38.48  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 50.04/38.48  tff(f_111, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_2)).
% 50.04/38.48  tff(f_80, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 50.04/38.48  tff(c_68, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 50.04/38.48  tff(c_6, plain, (![A_5]: (m1_subset_1('#skF_1'(A_5), A_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 50.04/38.48  tff(c_56, plain, (m1_subset_1('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 50.04/38.48  tff(c_58, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 50.04/38.48  tff(c_99, plain, (![C_68, A_69, B_70]: (v1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 50.04/38.48  tff(c_120, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_99])).
% 50.04/38.48  tff(c_60, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_164])).
% 50.04/38.48  tff(c_52, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_164])).
% 50.04/38.48  tff(c_64, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 50.04/38.48  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 50.04/38.48  tff(c_588, plain, (![A_131, B_132, C_133]: (k1_relset_1(A_131, B_132, C_133)=k1_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 50.04/38.48  tff(c_608, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_588])).
% 50.04/38.48  tff(c_4358, plain, (![B_370, A_371, C_372]: (k1_xboole_0=B_370 | k1_relset_1(A_371, B_370, C_372)=A_371 | ~v1_funct_2(C_372, A_371, B_370) | ~m1_subset_1(C_372, k1_zfmisc_1(k2_zfmisc_1(A_371, B_370))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 50.04/38.48  tff(c_4365, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_4358])).
% 50.04/38.48  tff(c_4380, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_608, c_4365])).
% 50.04/38.48  tff(c_4435, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_4380])).
% 50.04/38.48  tff(c_119, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_99])).
% 50.04/38.48  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_164])).
% 50.04/38.48  tff(c_10, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 50.04/38.48  tff(c_227453, plain, (![B_7161, C_7162, A_7163]: (k1_funct_1(k5_relat_1(B_7161, C_7162), A_7163)=k1_funct_1(C_7162, k1_funct_1(B_7161, A_7163)) | ~r2_hidden(A_7163, k1_relat_1(B_7161)) | ~v1_funct_1(C_7162) | ~v1_relat_1(C_7162) | ~v1_funct_1(B_7161) | ~v1_relat_1(B_7161))), inference(cnfTransformation, [status(thm)], [f_75])).
% 50.04/38.48  tff(c_231061, plain, (![B_7342, C_7343, A_7344]: (k1_funct_1(k5_relat_1(B_7342, C_7343), A_7344)=k1_funct_1(C_7343, k1_funct_1(B_7342, A_7344)) | ~v1_funct_1(C_7343) | ~v1_relat_1(C_7343) | ~v1_funct_1(B_7342) | ~v1_relat_1(B_7342) | v1_xboole_0(k1_relat_1(B_7342)) | ~m1_subset_1(A_7344, k1_relat_1(B_7342)))), inference(resolution, [status(thm)], [c_10, c_227453])).
% 50.04/38.48  tff(c_231065, plain, (![C_7343, A_7344]: (k1_funct_1(k5_relat_1('#skF_5', C_7343), A_7344)=k1_funct_1(C_7343, k1_funct_1('#skF_5', A_7344)) | ~v1_funct_1(C_7343) | ~v1_relat_1(C_7343) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | v1_xboole_0(k1_relat_1('#skF_5')) | ~m1_subset_1(A_7344, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4435, c_231061])).
% 50.04/38.48  tff(c_231075, plain, (![C_7343, A_7344]: (k1_funct_1(k5_relat_1('#skF_5', C_7343), A_7344)=k1_funct_1(C_7343, k1_funct_1('#skF_5', A_7344)) | ~v1_funct_1(C_7343) | ~v1_relat_1(C_7343) | v1_xboole_0('#skF_3') | ~m1_subset_1(A_7344, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4435, c_119, c_66, c_231065])).
% 50.04/38.48  tff(c_237306, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_231075])).
% 50.04/38.48  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 50.04/38.48  tff(c_237309, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_237306, c_2])).
% 50.04/38.48  tff(c_237313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_237309])).
% 50.04/38.48  tff(c_237314, plain, (![C_7343, A_7344]: (k1_funct_1(k5_relat_1('#skF_5', C_7343), A_7344)=k1_funct_1(C_7343, k1_funct_1('#skF_5', A_7344)) | ~v1_funct_1(C_7343) | ~v1_relat_1(C_7343) | ~m1_subset_1(A_7344, '#skF_3'))), inference(splitRight, [status(thm)], [c_231075])).
% 50.04/38.48  tff(c_4532, plain, (![B_377, C_378, A_379]: (k1_funct_1(k5_relat_1(B_377, C_378), A_379)=k1_funct_1(C_378, k1_funct_1(B_377, A_379)) | ~r2_hidden(A_379, k1_relat_1(B_377)) | ~v1_funct_1(C_378) | ~v1_relat_1(C_378) | ~v1_funct_1(B_377) | ~v1_relat_1(B_377))), inference(cnfTransformation, [status(thm)], [f_75])).
% 50.04/38.48  tff(c_102356, plain, (![B_3541, C_3542, A_3543]: (k1_funct_1(k5_relat_1(B_3541, C_3542), A_3543)=k1_funct_1(C_3542, k1_funct_1(B_3541, A_3543)) | ~v1_funct_1(C_3542) | ~v1_relat_1(C_3542) | ~v1_funct_1(B_3541) | ~v1_relat_1(B_3541) | v1_xboole_0(k1_relat_1(B_3541)) | ~m1_subset_1(A_3543, k1_relat_1(B_3541)))), inference(resolution, [status(thm)], [c_10, c_4532])).
% 50.04/38.48  tff(c_102358, plain, (![C_3542, A_3543]: (k1_funct_1(k5_relat_1('#skF_5', C_3542), A_3543)=k1_funct_1(C_3542, k1_funct_1('#skF_5', A_3543)) | ~v1_funct_1(C_3542) | ~v1_relat_1(C_3542) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | v1_xboole_0(k1_relat_1('#skF_5')) | ~m1_subset_1(A_3543, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4435, c_102356])).
% 50.04/38.48  tff(c_102365, plain, (![C_3542, A_3543]: (k1_funct_1(k5_relat_1('#skF_5', C_3542), A_3543)=k1_funct_1(C_3542, k1_funct_1('#skF_5', A_3543)) | ~v1_funct_1(C_3542) | ~v1_relat_1(C_3542) | v1_xboole_0('#skF_3') | ~m1_subset_1(A_3543, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4435, c_119, c_66, c_102358])).
% 50.04/38.48  tff(c_110403, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_102365])).
% 50.04/38.48  tff(c_110406, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_110403, c_2])).
% 50.04/38.48  tff(c_110410, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_110406])).
% 50.04/38.48  tff(c_110411, plain, (![C_3542, A_3543]: (k1_funct_1(k5_relat_1('#skF_5', C_3542), A_3543)=k1_funct_1(C_3542, k1_funct_1('#skF_5', A_3543)) | ~v1_funct_1(C_3542) | ~v1_relat_1(C_3542) | ~m1_subset_1(A_3543, '#skF_3'))), inference(splitRight, [status(thm)], [c_102365])).
% 50.04/38.48  tff(c_8, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 50.04/38.48  tff(c_77, plain, (![A_66, B_67]: (r1_tarski(A_66, B_67) | ~m1_subset_1(A_66, k1_zfmisc_1(B_67)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 50.04/38.48  tff(c_97, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(resolution, [status(thm)], [c_8, c_77])).
% 50.04/38.48  tff(c_86243, plain, (![B_3053, C_3054, A_3055]: (k1_funct_1(k5_relat_1(B_3053, C_3054), A_3055)=k1_funct_1(C_3054, k1_funct_1(B_3053, A_3055)) | ~v1_funct_1(C_3054) | ~v1_relat_1(C_3054) | ~v1_funct_1(B_3053) | ~v1_relat_1(B_3053) | v1_xboole_0(k1_relat_1(B_3053)) | ~m1_subset_1(A_3055, k1_relat_1(B_3053)))), inference(resolution, [status(thm)], [c_10, c_4532])).
% 50.04/38.48  tff(c_86247, plain, (![C_3054, A_3055]: (k1_funct_1(k5_relat_1('#skF_5', C_3054), A_3055)=k1_funct_1(C_3054, k1_funct_1('#skF_5', A_3055)) | ~v1_funct_1(C_3054) | ~v1_relat_1(C_3054) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | v1_xboole_0(k1_relat_1('#skF_5')) | ~m1_subset_1(A_3055, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4435, c_86243])).
% 50.04/38.48  tff(c_86257, plain, (![C_3054, A_3055]: (k1_funct_1(k5_relat_1('#skF_5', C_3054), A_3055)=k1_funct_1(C_3054, k1_funct_1('#skF_5', A_3055)) | ~v1_funct_1(C_3054) | ~v1_relat_1(C_3054) | v1_xboole_0('#skF_3') | ~m1_subset_1(A_3055, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4435, c_119, c_66, c_86247])).
% 50.04/38.48  tff(c_95739, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_86257])).
% 50.04/38.48  tff(c_95742, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_95739, c_2])).
% 50.04/38.48  tff(c_95746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_95742])).
% 50.04/38.48  tff(c_95747, plain, (![C_3054, A_3055]: (k1_funct_1(k5_relat_1('#skF_5', C_3054), A_3055)=k1_funct_1(C_3054, k1_funct_1('#skF_5', A_3055)) | ~v1_funct_1(C_3054) | ~v1_relat_1(C_3054) | ~m1_subset_1(A_3055, '#skF_3'))), inference(splitRight, [status(thm)], [c_86257])).
% 50.04/38.48  tff(c_4571, plain, (![E_381, B_386, C_383, D_384, F_385, A_382]: (k1_partfun1(A_382, B_386, C_383, D_384, E_381, F_385)=k5_relat_1(E_381, F_385) | ~m1_subset_1(F_385, k1_zfmisc_1(k2_zfmisc_1(C_383, D_384))) | ~v1_funct_1(F_385) | ~m1_subset_1(E_381, k1_zfmisc_1(k2_zfmisc_1(A_382, B_386))) | ~v1_funct_1(E_381))), inference(cnfTransformation, [status(thm)], [f_139])).
% 50.04/38.48  tff(c_4578, plain, (![A_382, B_386, E_381]: (k1_partfun1(A_382, B_386, '#skF_4', '#skF_2', E_381, '#skF_6')=k5_relat_1(E_381, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_381, k1_zfmisc_1(k2_zfmisc_1(A_382, B_386))) | ~v1_funct_1(E_381))), inference(resolution, [status(thm)], [c_58, c_4571])).
% 50.04/38.48  tff(c_84732, plain, (![A_2999, B_3000, E_3001]: (k1_partfun1(A_2999, B_3000, '#skF_4', '#skF_2', E_3001, '#skF_6')=k5_relat_1(E_3001, '#skF_6') | ~m1_subset_1(E_3001, k1_zfmisc_1(k2_zfmisc_1(A_2999, B_3000))) | ~v1_funct_1(E_3001))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_4578])).
% 50.04/38.48  tff(c_84739, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_84732])).
% 50.04/38.48  tff(c_84754, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_84739])).
% 50.04/38.48  tff(c_609, plain, (k1_relset_1('#skF_4', '#skF_2', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_588])).
% 50.04/38.48  tff(c_54, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 50.04/38.48  tff(c_617, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_609, c_54])).
% 50.04/38.48  tff(c_190, plain, (![C_83, A_84, B_85]: (v4_relat_1(C_83, A_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 50.04/38.48  tff(c_211, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_190])).
% 50.04/38.48  tff(c_95, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_77])).
% 50.04/38.48  tff(c_264, plain, (![A_97, C_98, B_99]: (r1_tarski(A_97, C_98) | ~r1_tarski(B_99, C_98) | ~r1_tarski(A_97, B_99))), inference(cnfTransformation, [status(thm)], [f_35])).
% 50.04/38.48  tff(c_276, plain, (![A_97]: (r1_tarski(A_97, k2_zfmisc_1('#skF_3', '#skF_4')) | ~r1_tarski(A_97, '#skF_5'))), inference(resolution, [status(thm)], [c_95, c_264])).
% 50.04/38.48  tff(c_14, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 50.04/38.48  tff(c_4477, plain, (![B_373, C_374, A_375]: (k1_xboole_0=B_373 | v1_funct_2(C_374, A_375, B_373) | k1_relset_1(A_375, B_373, C_374)!=A_375 | ~m1_subset_1(C_374, k1_zfmisc_1(k2_zfmisc_1(A_375, B_373))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 50.04/38.48  tff(c_69050, plain, (![B_2489, A_2490, A_2491]: (k1_xboole_0=B_2489 | v1_funct_2(A_2490, A_2491, B_2489) | k1_relset_1(A_2491, B_2489, A_2490)!=A_2491 | ~r1_tarski(A_2490, k2_zfmisc_1(A_2491, B_2489)))), inference(resolution, [status(thm)], [c_14, c_4477])).
% 50.04/38.48  tff(c_69110, plain, (![A_97]: (k1_xboole_0='#skF_4' | v1_funct_2(A_97, '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', A_97)!='#skF_3' | ~r1_tarski(A_97, '#skF_5'))), inference(resolution, [status(thm)], [c_276, c_69050])).
% 50.04/38.48  tff(c_94836, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_69110])).
% 50.04/38.48  tff(c_334, plain, (![B_108, A_109]: (r1_tarski(k1_relat_1(B_108), A_109) | ~v4_relat_1(B_108, A_109) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_62])).
% 50.04/38.48  tff(c_4, plain, (![A_2, C_4, B_3]: (r1_tarski(A_2, C_4) | ~r1_tarski(B_3, C_4) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 50.04/38.48  tff(c_4970, plain, (![A_423, A_424, B_425]: (r1_tarski(A_423, A_424) | ~r1_tarski(A_423, k1_relat_1(B_425)) | ~v4_relat_1(B_425, A_424) | ~v1_relat_1(B_425))), inference(resolution, [status(thm)], [c_334, c_4])).
% 50.04/38.48  tff(c_4988, plain, (![A_424]: (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), A_424) | ~v4_relat_1('#skF_6', A_424) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_617, c_4970])).
% 50.04/38.48  tff(c_5024, plain, (![A_426]: (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), A_426) | ~v4_relat_1('#skF_6', A_426))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_4988])).
% 50.04/38.48  tff(c_278, plain, (![A_97, A_7]: (r1_tarski(A_97, A_7) | ~r1_tarski(A_97, k1_xboole_0))), inference(resolution, [status(thm)], [c_97, c_264])).
% 50.04/38.48  tff(c_5093, plain, (![A_7]: (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), A_7) | ~v4_relat_1('#skF_6', k1_xboole_0))), inference(resolution, [status(thm)], [c_5024, c_278])).
% 50.04/38.48  tff(c_68123, plain, (~v4_relat_1('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_5093])).
% 50.04/38.48  tff(c_94860, plain, (~v4_relat_1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94836, c_68123])).
% 50.04/38.48  tff(c_94896, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_211, c_94860])).
% 50.04/38.48  tff(c_94898, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_69110])).
% 50.04/38.48  tff(c_4678, plain, (![A_397, C_396, B_395, D_398, E_394]: (k1_partfun1(A_397, B_395, B_395, C_396, D_398, E_394)=k8_funct_2(A_397, B_395, C_396, D_398, E_394) | k1_xboole_0=B_395 | ~r1_tarski(k2_relset_1(A_397, B_395, D_398), k1_relset_1(B_395, C_396, E_394)) | ~m1_subset_1(E_394, k1_zfmisc_1(k2_zfmisc_1(B_395, C_396))) | ~v1_funct_1(E_394) | ~m1_subset_1(D_398, k1_zfmisc_1(k2_zfmisc_1(A_397, B_395))) | ~v1_funct_2(D_398, A_397, B_395) | ~v1_funct_1(D_398))), inference(cnfTransformation, [status(thm)], [f_111])).
% 50.04/38.48  tff(c_4687, plain, (![A_397, D_398]: (k1_partfun1(A_397, '#skF_4', '#skF_4', '#skF_2', D_398, '#skF_6')=k8_funct_2(A_397, '#skF_4', '#skF_2', D_398, '#skF_6') | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relset_1(A_397, '#skF_4', D_398), k1_relat_1('#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1(D_398, k1_zfmisc_1(k2_zfmisc_1(A_397, '#skF_4'))) | ~v1_funct_2(D_398, A_397, '#skF_4') | ~v1_funct_1(D_398))), inference(superposition, [status(thm), theory('equality')], [c_609, c_4678])).
% 50.04/38.48  tff(c_4694, plain, (![A_397, D_398]: (k1_partfun1(A_397, '#skF_4', '#skF_4', '#skF_2', D_398, '#skF_6')=k8_funct_2(A_397, '#skF_4', '#skF_2', D_398, '#skF_6') | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relset_1(A_397, '#skF_4', D_398), k1_relat_1('#skF_6')) | ~m1_subset_1(D_398, k1_zfmisc_1(k2_zfmisc_1(A_397, '#skF_4'))) | ~v1_funct_2(D_398, A_397, '#skF_4') | ~v1_funct_1(D_398))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_4687])).
% 50.04/38.48  tff(c_100447, plain, (![A_3433, D_3434]: (k1_partfun1(A_3433, '#skF_4', '#skF_4', '#skF_2', D_3434, '#skF_6')=k8_funct_2(A_3433, '#skF_4', '#skF_2', D_3434, '#skF_6') | ~r1_tarski(k2_relset_1(A_3433, '#skF_4', D_3434), k1_relat_1('#skF_6')) | ~m1_subset_1(D_3434, k1_zfmisc_1(k2_zfmisc_1(A_3433, '#skF_4'))) | ~v1_funct_2(D_3434, A_3433, '#skF_4') | ~v1_funct_1(D_3434))), inference(negUnitSimplification, [status(thm)], [c_94898, c_4694])).
% 50.04/38.48  tff(c_100454, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_617, c_100447])).
% 50.04/38.48  tff(c_100460, plain, (k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_84754, c_100454])).
% 50.04/38.48  tff(c_50, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 50.04/38.48  tff(c_100461, plain, (k1_funct_1(k5_relat_1('#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_100460, c_50])).
% 50.04/38.48  tff(c_100468, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_95747, c_100461])).
% 50.04/38.48  tff(c_100475, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_120, c_60, c_100468])).
% 50.04/38.48  tff(c_100508, plain, (![A_3436]: (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), A_3436))), inference(splitRight, [status(thm)], [c_5093])).
% 50.04/38.48  tff(c_126, plain, (![A_75, B_76]: (r2_hidden(A_75, B_76) | v1_xboole_0(B_76) | ~m1_subset_1(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_46])).
% 50.04/38.48  tff(c_24, plain, (![B_22, A_21]: (~r1_tarski(B_22, A_21) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_80])).
% 50.04/38.48  tff(c_130, plain, (![B_76, A_75]: (~r1_tarski(B_76, A_75) | v1_xboole_0(B_76) | ~m1_subset_1(A_75, B_76))), inference(resolution, [status(thm)], [c_126, c_24])).
% 50.04/38.48  tff(c_100595, plain, (![A_3436]: (v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(A_3436, k2_relset_1('#skF_3', '#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_100508, c_130])).
% 50.04/38.48  tff(c_106975, plain, (![A_3658]: (~m1_subset_1(A_3658, k2_relset_1('#skF_3', '#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_100595])).
% 50.04/38.48  tff(c_106985, plain, $false, inference(resolution, [status(thm)], [c_6, c_106975])).
% 50.04/38.48  tff(c_106986, plain, (v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_100595])).
% 50.04/38.48  tff(c_106990, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_106986, c_2])).
% 50.04/38.48  tff(c_101456, plain, (![A_3472, B_3473, E_3474]: (k1_partfun1(A_3472, B_3473, '#skF_4', '#skF_2', E_3474, '#skF_6')=k5_relat_1(E_3474, '#skF_6') | ~m1_subset_1(E_3474, k1_zfmisc_1(k2_zfmisc_1(A_3472, B_3473))) | ~v1_funct_1(E_3474))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_4578])).
% 50.04/38.48  tff(c_101463, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_101456])).
% 50.04/38.48  tff(c_101478, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_101463])).
% 50.04/38.48  tff(c_100477, plain, (v4_relat_1('#skF_6', k1_xboole_0)), inference(splitRight, [status(thm)], [c_5093])).
% 50.04/38.48  tff(c_4233, plain, (![B_358, A_359]: (r1_tarski(k1_relat_1(B_358), A_359) | ~v4_relat_1(B_358, k1_xboole_0) | ~v1_relat_1(B_358))), inference(resolution, [status(thm)], [c_334, c_278])).
% 50.04/38.48  tff(c_18, plain, (![B_16, A_15]: (v4_relat_1(B_16, A_15) | ~r1_tarski(k1_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 50.04/38.48  tff(c_4287, plain, (![B_358, A_359]: (v4_relat_1(B_358, A_359) | ~v4_relat_1(B_358, k1_xboole_0) | ~v1_relat_1(B_358))), inference(resolution, [status(thm)], [c_4233, c_18])).
% 50.04/38.48  tff(c_100479, plain, (![A_359]: (v4_relat_1('#skF_6', A_359) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_100477, c_4287])).
% 50.04/38.48  tff(c_100482, plain, (![A_359]: (v4_relat_1('#skF_6', A_359))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_100479])).
% 50.04/38.48  tff(c_20, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(B_16), A_15) | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 50.04/38.48  tff(c_98, plain, (![B_67]: (r1_tarski('#skF_1'(k1_zfmisc_1(B_67)), B_67))), inference(resolution, [status(thm)], [c_6, c_77])).
% 50.04/38.48  tff(c_399, plain, (![A_114, B_115]: (r1_tarski(A_114, B_115) | ~r1_tarski(A_114, '#skF_1'(k1_zfmisc_1(B_115))))), inference(resolution, [status(thm)], [c_98, c_264])).
% 50.04/38.48  tff(c_102985, plain, (![B_3591, B_3592]: (r1_tarski(k1_relat_1(B_3591), B_3592) | ~v4_relat_1(B_3591, '#skF_1'(k1_zfmisc_1(B_3592))) | ~v1_relat_1(B_3591))), inference(resolution, [status(thm)], [c_20, c_399])).
% 50.04/38.48  tff(c_103077, plain, (![B_3592]: (r1_tarski(k1_relat_1('#skF_6'), B_3592) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_100482, c_102985])).
% 50.04/38.48  tff(c_103218, plain, (![B_3595]: (r1_tarski(k1_relat_1('#skF_6'), B_3595))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_103077])).
% 50.04/38.48  tff(c_103348, plain, (![B_3595]: (v1_xboole_0(k1_relat_1('#skF_6')) | ~m1_subset_1(B_3595, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_103218, c_130])).
% 50.04/38.48  tff(c_103777, plain, (![B_3600]: (~m1_subset_1(B_3600, k1_relat_1('#skF_6')))), inference(splitLeft, [status(thm)], [c_103348])).
% 50.04/38.48  tff(c_103787, plain, $false, inference(resolution, [status(thm)], [c_6, c_103777])).
% 50.04/38.48  tff(c_103788, plain, (v1_xboole_0(k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_103348])).
% 50.04/38.48  tff(c_103792, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_103788, c_2])).
% 50.04/38.48  tff(c_4368, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_4', '#skF_2', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_4358])).
% 50.04/38.48  tff(c_4382, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_609, c_4368])).
% 50.04/38.48  tff(c_4436, plain, (~v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_4382])).
% 50.04/38.48  tff(c_4487, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_6', '#skF_4', '#skF_2') | k1_relset_1('#skF_4', '#skF_2', '#skF_6')!='#skF_4'), inference(resolution, [status(thm)], [c_58, c_4477])).
% 50.04/38.48  tff(c_4501, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_6', '#skF_4', '#skF_2') | k1_relat_1('#skF_6')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_609, c_4487])).
% 50.04/38.48  tff(c_4502, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_6')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_4436, c_4501])).
% 50.04/38.48  tff(c_4506, plain, (k1_relat_1('#skF_6')!='#skF_4'), inference(splitLeft, [status(thm)], [c_4502])).
% 50.04/38.48  tff(c_103820, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_103792, c_4506])).
% 50.04/38.48  tff(c_113389, plain, (![A_397, D_398]: (k1_partfun1(A_397, '#skF_4', '#skF_4', '#skF_2', D_398, '#skF_6')=k8_funct_2(A_397, '#skF_4', '#skF_2', D_398, '#skF_6') | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relset_1(A_397, '#skF_4', D_398), k1_xboole_0) | ~m1_subset_1(D_398, k1_zfmisc_1(k2_zfmisc_1(A_397, '#skF_4'))) | ~v1_funct_2(D_398, A_397, '#skF_4') | ~v1_funct_1(D_398))), inference(demodulation, [status(thm), theory('equality')], [c_103792, c_4694])).
% 50.04/38.48  tff(c_113391, plain, (![A_3875, D_3876]: (k1_partfun1(A_3875, '#skF_4', '#skF_4', '#skF_2', D_3876, '#skF_6')=k8_funct_2(A_3875, '#skF_4', '#skF_2', D_3876, '#skF_6') | ~r1_tarski(k2_relset_1(A_3875, '#skF_4', D_3876), k1_xboole_0) | ~m1_subset_1(D_3876, k1_zfmisc_1(k2_zfmisc_1(A_3875, '#skF_4'))) | ~v1_funct_2(D_3876, A_3875, '#skF_4') | ~v1_funct_1(D_3876))), inference(negUnitSimplification, [status(thm)], [c_103820, c_113389])).
% 50.04/38.48  tff(c_113402, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_xboole_0) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_113391])).
% 50.04/38.48  tff(c_113415, plain, (k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_97, c_106990, c_101478, c_113402])).
% 50.04/38.48  tff(c_113418, plain, (k1_funct_1(k5_relat_1('#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_113415, c_50])).
% 50.04/38.48  tff(c_113425, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_110411, c_113418])).
% 50.04/38.48  tff(c_113432, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_120, c_60, c_113425])).
% 50.04/38.48  tff(c_113434, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_4502])).
% 50.04/38.48  tff(c_113481, plain, (![A_15]: (v4_relat_1('#skF_6', A_15) | ~r1_tarski('#skF_4', A_15) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_113434, c_18])).
% 50.04/38.48  tff(c_113491, plain, (![A_15]: (v4_relat_1('#skF_6', A_15) | ~r1_tarski('#skF_4', A_15))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_113481])).
% 50.04/38.48  tff(c_113433, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_4502])).
% 50.04/38.48  tff(c_143170, plain, (![B_4742, A_4743]: (v4_relat_1(B_4742, A_4743) | ~v4_relat_1(B_4742, '#skF_2') | ~v1_relat_1(B_4742))), inference(demodulation, [status(thm), theory('equality')], [c_113433, c_4287])).
% 50.04/38.48  tff(c_143176, plain, (![A_4743]: (v4_relat_1('#skF_6', A_4743) | ~v1_relat_1('#skF_6') | ~r1_tarski('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_113491, c_143170])).
% 50.04/38.48  tff(c_143191, plain, (![A_4743]: (v4_relat_1('#skF_6', A_4743) | ~r1_tarski('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_143176])).
% 50.04/38.48  tff(c_143201, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_143191])).
% 50.04/38.48  tff(c_113459, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_113433, c_52])).
% 50.04/38.48  tff(c_113537, plain, (![B_3879, C_3880, A_3881]: (k1_funct_1(k5_relat_1(B_3879, C_3880), A_3881)=k1_funct_1(C_3880, k1_funct_1(B_3879, A_3881)) | ~r2_hidden(A_3881, k1_relat_1(B_3879)) | ~v1_funct_1(C_3880) | ~v1_relat_1(C_3880) | ~v1_funct_1(B_3879) | ~v1_relat_1(B_3879))), inference(cnfTransformation, [status(thm)], [f_75])).
% 50.04/38.48  tff(c_147090, plain, (![B_4904, C_4905, A_4906]: (k1_funct_1(k5_relat_1(B_4904, C_4905), A_4906)=k1_funct_1(C_4905, k1_funct_1(B_4904, A_4906)) | ~v1_funct_1(C_4905) | ~v1_relat_1(C_4905) | ~v1_funct_1(B_4904) | ~v1_relat_1(B_4904) | v1_xboole_0(k1_relat_1(B_4904)) | ~m1_subset_1(A_4906, k1_relat_1(B_4904)))), inference(resolution, [status(thm)], [c_10, c_113537])).
% 50.04/38.48  tff(c_147096, plain, (![C_4905, A_4906]: (k1_funct_1(k5_relat_1('#skF_5', C_4905), A_4906)=k1_funct_1(C_4905, k1_funct_1('#skF_5', A_4906)) | ~v1_funct_1(C_4905) | ~v1_relat_1(C_4905) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | v1_xboole_0(k1_relat_1('#skF_5')) | ~m1_subset_1(A_4906, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4435, c_147090])).
% 50.04/38.48  tff(c_147106, plain, (![C_4905, A_4906]: (k1_funct_1(k5_relat_1('#skF_5', C_4905), A_4906)=k1_funct_1(C_4905, k1_funct_1('#skF_5', A_4906)) | ~v1_funct_1(C_4905) | ~v1_relat_1(C_4905) | v1_xboole_0('#skF_3') | ~m1_subset_1(A_4906, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4435, c_119, c_66, c_147096])).
% 50.04/38.48  tff(c_163296, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_147106])).
% 50.04/38.48  tff(c_113457, plain, (![A_1]: (A_1='#skF_2' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_113433, c_2])).
% 50.04/38.48  tff(c_163299, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_163296, c_113457])).
% 50.04/38.48  tff(c_163303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_113459, c_163299])).
% 50.04/38.48  tff(c_163304, plain, (![C_4905, A_4906]: (k1_funct_1(k5_relat_1('#skF_5', C_4905), A_4906)=k1_funct_1(C_4905, k1_funct_1('#skF_5', A_4906)) | ~v1_funct_1(C_4905) | ~v1_relat_1(C_4905) | ~m1_subset_1(A_4906, '#skF_3'))), inference(splitRight, [status(thm)], [c_147106])).
% 50.04/38.48  tff(c_113467, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_113434, c_617])).
% 50.04/38.48  tff(c_113620, plain, (![A_3886, B_3890, C_3887, E_3885, F_3889, D_3888]: (k1_partfun1(A_3886, B_3890, C_3887, D_3888, E_3885, F_3889)=k5_relat_1(E_3885, F_3889) | ~m1_subset_1(F_3889, k1_zfmisc_1(k2_zfmisc_1(C_3887, D_3888))) | ~v1_funct_1(F_3889) | ~m1_subset_1(E_3885, k1_zfmisc_1(k2_zfmisc_1(A_3886, B_3890))) | ~v1_funct_1(E_3885))), inference(cnfTransformation, [status(thm)], [f_139])).
% 50.04/38.48  tff(c_113630, plain, (![A_3886, B_3890, E_3885]: (k1_partfun1(A_3886, B_3890, '#skF_4', '#skF_2', E_3885, '#skF_6')=k5_relat_1(E_3885, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_3885, k1_zfmisc_1(k2_zfmisc_1(A_3886, B_3890))) | ~v1_funct_1(E_3885))), inference(resolution, [status(thm)], [c_58, c_113620])).
% 50.04/38.48  tff(c_144126, plain, (![A_4777, B_4778, E_4779]: (k1_partfun1(A_4777, B_4778, '#skF_4', '#skF_2', E_4779, '#skF_6')=k5_relat_1(E_4779, '#skF_6') | ~m1_subset_1(E_4779, k1_zfmisc_1(k2_zfmisc_1(A_4777, B_4778))) | ~v1_funct_1(E_4779))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_113630])).
% 50.04/38.48  tff(c_144137, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_144126])).
% 50.04/38.48  tff(c_144149, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_144137])).
% 50.04/38.48  tff(c_96, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_77])).
% 50.04/38.48  tff(c_277, plain, (![A_97]: (r1_tarski(A_97, k2_zfmisc_1('#skF_4', '#skF_2')) | ~r1_tarski(A_97, '#skF_6'))), inference(resolution, [status(thm)], [c_96, c_264])).
% 50.04/38.48  tff(c_702, plain, (![C_141, A_142]: (k1_xboole_0=C_141 | ~v1_funct_2(C_141, A_142, k1_xboole_0) | k1_xboole_0=A_142 | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_142, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 50.04/38.48  tff(c_715, plain, (![A_10, A_142]: (k1_xboole_0=A_10 | ~v1_funct_2(A_10, A_142, k1_xboole_0) | k1_xboole_0=A_142 | ~r1_tarski(A_10, k2_zfmisc_1(A_142, k1_xboole_0)))), inference(resolution, [status(thm)], [c_14, c_702])).
% 50.04/38.48  tff(c_143364, plain, (![A_4755, A_4756]: (A_4755='#skF_2' | ~v1_funct_2(A_4755, A_4756, '#skF_2') | A_4756='#skF_2' | ~r1_tarski(A_4755, k2_zfmisc_1(A_4756, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_113433, c_113433, c_113433, c_113433, c_715])).
% 50.04/38.48  tff(c_143388, plain, (![A_97]: (A_97='#skF_2' | ~v1_funct_2(A_97, '#skF_4', '#skF_2') | '#skF_2'='#skF_4' | ~r1_tarski(A_97, '#skF_6'))), inference(resolution, [status(thm)], [c_277, c_143364])).
% 50.04/38.48  tff(c_148124, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_143388])).
% 50.04/38.48  tff(c_143202, plain, (![A_4744, A_4745, B_4746]: (r1_tarski(A_4744, A_4745) | ~r1_tarski(A_4744, k1_relat_1(B_4746)) | ~v4_relat_1(B_4746, A_4745) | ~v1_relat_1(B_4746))), inference(resolution, [status(thm)], [c_334, c_4])).
% 50.04/38.48  tff(c_143209, plain, (![A_4744, A_4745]: (r1_tarski(A_4744, A_4745) | ~r1_tarski(A_4744, '#skF_4') | ~v4_relat_1('#skF_6', A_4745) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_113434, c_143202])).
% 50.04/38.48  tff(c_143393, plain, (![A_4757, A_4758]: (r1_tarski(A_4757, A_4758) | ~r1_tarski(A_4757, '#skF_4') | ~v4_relat_1('#skF_6', A_4758))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_143209])).
% 50.04/38.48  tff(c_143426, plain, (![A_4759]: (r1_tarski('#skF_1'(k1_zfmisc_1('#skF_4')), A_4759) | ~v4_relat_1('#skF_6', A_4759))), inference(resolution, [status(thm)], [c_98, c_143393])).
% 50.04/38.48  tff(c_113450, plain, (![A_97, A_7]: (r1_tarski(A_97, A_7) | ~r1_tarski(A_97, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_113433, c_278])).
% 50.04/38.48  tff(c_143499, plain, (![A_7]: (r1_tarski('#skF_1'(k1_zfmisc_1('#skF_4')), A_7) | ~v4_relat_1('#skF_6', '#skF_2'))), inference(resolution, [status(thm)], [c_143426, c_113450])).
% 50.04/38.48  tff(c_143516, plain, (~v4_relat_1('#skF_6', '#skF_2')), inference(splitLeft, [status(thm)], [c_143499])).
% 50.04/38.48  tff(c_148194, plain, (~v4_relat_1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_148124, c_143516])).
% 50.04/38.48  tff(c_148235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_211, c_148194])).
% 50.04/38.48  tff(c_148237, plain, ('#skF_2'!='#skF_4'), inference(splitRight, [status(thm)], [c_143388])).
% 50.04/38.48  tff(c_113468, plain, (k1_relset_1('#skF_4', '#skF_2', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_113434, c_609])).
% 50.04/38.48  tff(c_34, plain, (![B_33, C_34, E_37, A_32, D_35]: (k1_partfun1(A_32, B_33, B_33, C_34, D_35, E_37)=k8_funct_2(A_32, B_33, C_34, D_35, E_37) | k1_xboole_0=B_33 | ~r1_tarski(k2_relset_1(A_32, B_33, D_35), k1_relset_1(B_33, C_34, E_37)) | ~m1_subset_1(E_37, k1_zfmisc_1(k2_zfmisc_1(B_33, C_34))) | ~v1_funct_1(E_37) | ~m1_subset_1(D_35, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_2(D_35, A_32, B_33) | ~v1_funct_1(D_35))), inference(cnfTransformation, [status(thm)], [f_111])).
% 50.04/38.48  tff(c_113693, plain, (![A_3897, E_3894, D_3898, C_3896, B_3895]: (k1_partfun1(A_3897, B_3895, B_3895, C_3896, D_3898, E_3894)=k8_funct_2(A_3897, B_3895, C_3896, D_3898, E_3894) | B_3895='#skF_2' | ~r1_tarski(k2_relset_1(A_3897, B_3895, D_3898), k1_relset_1(B_3895, C_3896, E_3894)) | ~m1_subset_1(E_3894, k1_zfmisc_1(k2_zfmisc_1(B_3895, C_3896))) | ~v1_funct_1(E_3894) | ~m1_subset_1(D_3898, k1_zfmisc_1(k2_zfmisc_1(A_3897, B_3895))) | ~v1_funct_2(D_3898, A_3897, B_3895) | ~v1_funct_1(D_3898))), inference(demodulation, [status(thm), theory('equality')], [c_113433, c_34])).
% 50.04/38.48  tff(c_113699, plain, (![A_3897, D_3898]: (k1_partfun1(A_3897, '#skF_4', '#skF_4', '#skF_2', D_3898, '#skF_6')=k8_funct_2(A_3897, '#skF_4', '#skF_2', D_3898, '#skF_6') | '#skF_2'='#skF_4' | ~r1_tarski(k2_relset_1(A_3897, '#skF_4', D_3898), '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1(D_3898, k1_zfmisc_1(k2_zfmisc_1(A_3897, '#skF_4'))) | ~v1_funct_2(D_3898, A_3897, '#skF_4') | ~v1_funct_1(D_3898))), inference(superposition, [status(thm), theory('equality')], [c_113468, c_113693])).
% 50.04/38.48  tff(c_113706, plain, (![A_3897, D_3898]: (k1_partfun1(A_3897, '#skF_4', '#skF_4', '#skF_2', D_3898, '#skF_6')=k8_funct_2(A_3897, '#skF_4', '#skF_2', D_3898, '#skF_6') | '#skF_2'='#skF_4' | ~r1_tarski(k2_relset_1(A_3897, '#skF_4', D_3898), '#skF_4') | ~m1_subset_1(D_3898, k1_zfmisc_1(k2_zfmisc_1(A_3897, '#skF_4'))) | ~v1_funct_2(D_3898, A_3897, '#skF_4') | ~v1_funct_1(D_3898))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_113699])).
% 50.04/38.48  tff(c_168508, plain, (![A_5403, D_5404]: (k1_partfun1(A_5403, '#skF_4', '#skF_4', '#skF_2', D_5404, '#skF_6')=k8_funct_2(A_5403, '#skF_4', '#skF_2', D_5404, '#skF_6') | ~r1_tarski(k2_relset_1(A_5403, '#skF_4', D_5404), '#skF_4') | ~m1_subset_1(D_5404, k1_zfmisc_1(k2_zfmisc_1(A_5403, '#skF_4'))) | ~v1_funct_2(D_5404, A_5403, '#skF_4') | ~v1_funct_1(D_5404))), inference(negUnitSimplification, [status(thm)], [c_148237, c_113706])).
% 50.04/38.48  tff(c_168523, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_168508])).
% 50.04/38.48  tff(c_168533, plain, (k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_113467, c_144149, c_168523])).
% 50.04/38.48  tff(c_168535, plain, (k1_funct_1(k5_relat_1('#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_168533, c_50])).
% 50.04/38.48  tff(c_168542, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_163304, c_168535])).
% 50.04/38.48  tff(c_168549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_120, c_60, c_168542])).
% 50.04/38.48  tff(c_168551, plain, (v4_relat_1('#skF_6', '#skF_2')), inference(splitRight, [status(thm)], [c_143499])).
% 50.04/38.48  tff(c_113478, plain, (![A_15]: (r1_tarski('#skF_4', A_15) | ~v4_relat_1('#skF_6', A_15) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_113434, c_20])).
% 50.04/38.48  tff(c_113489, plain, (![A_15]: (r1_tarski('#skF_4', A_15) | ~v4_relat_1('#skF_6', A_15))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_113478])).
% 50.04/38.48  tff(c_168556, plain, (r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_168551, c_113489])).
% 50.04/38.48  tff(c_168563, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143201, c_168556])).
% 50.04/38.48  tff(c_168564, plain, (![A_4743]: (v4_relat_1('#skF_6', A_4743))), inference(splitRight, [status(thm)], [c_143191])).
% 50.04/38.48  tff(c_168628, plain, (![A_5409]: (r1_tarski('#skF_4', A_5409))), inference(demodulation, [status(thm), theory('equality')], [c_168564, c_113489])).
% 50.04/38.48  tff(c_168668, plain, (![A_5409]: (v1_xboole_0('#skF_4') | ~m1_subset_1(A_5409, '#skF_4'))), inference(resolution, [status(thm)], [c_168628, c_130])).
% 50.04/38.48  tff(c_168731, plain, (![A_5414]: (~m1_subset_1(A_5414, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_168668])).
% 50.04/38.48  tff(c_168736, plain, $false, inference(resolution, [status(thm)], [c_6, c_168731])).
% 50.04/38.48  tff(c_168737, plain, (k1_relat_1('#skF_6')='#skF_4' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_4382])).
% 50.04/38.48  tff(c_168778, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_168737])).
% 50.04/38.48  tff(c_121, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_99])).
% 50.04/38.48  tff(c_168797, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_168778, c_121])).
% 50.04/38.48  tff(c_168738, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_4382])).
% 50.04/38.48  tff(c_170072, plain, (![A_5485, A_5486]: (A_5485='#skF_2' | ~v1_funct_2(A_5485, A_5486, '#skF_2') | A_5486='#skF_2' | ~r1_tarski(A_5485, k2_zfmisc_1(A_5486, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_168778, c_168778, c_168778, c_168778, c_715])).
% 50.04/38.48  tff(c_170106, plain, ('#skF_6'='#skF_2' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_2') | '#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_96, c_170072])).
% 50.04/38.48  tff(c_170117, plain, ('#skF_6'='#skF_2' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_168738, c_170106])).
% 50.04/38.48  tff(c_170118, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_170117])).
% 50.04/38.48  tff(c_154, plain, (![B_80, A_81]: (~r1_tarski(B_80, A_81) | v1_xboole_0(B_80) | ~m1_subset_1(A_81, B_80))), inference(resolution, [status(thm)], [c_126, c_24])).
% 50.04/38.48  tff(c_173, plain, (![A_7]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_97, c_154])).
% 50.04/38.48  tff(c_176, plain, (![A_82]: (~m1_subset_1(A_82, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_173])).
% 50.04/38.48  tff(c_181, plain, $false, inference(resolution, [status(thm)], [c_6, c_176])).
% 50.04/38.48  tff(c_182, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_173])).
% 50.04/38.48  tff(c_168795, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_168778, c_182])).
% 50.04/38.48  tff(c_170141, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_170118, c_168795])).
% 50.04/38.48  tff(c_170157, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_170141])).
% 50.04/38.48  tff(c_170158, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_170117])).
% 50.04/38.48  tff(c_170195, plain, (v1_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_170158, c_60])).
% 50.04/38.48  tff(c_168801, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_168778, c_52])).
% 50.04/38.48  tff(c_168952, plain, (![B_5423, C_5424, A_5425]: (k1_funct_1(k5_relat_1(B_5423, C_5424), A_5425)=k1_funct_1(C_5424, k1_funct_1(B_5423, A_5425)) | ~r2_hidden(A_5425, k1_relat_1(B_5423)) | ~v1_funct_1(C_5424) | ~v1_relat_1(C_5424) | ~v1_funct_1(B_5423) | ~v1_relat_1(B_5423))), inference(cnfTransformation, [status(thm)], [f_75])).
% 50.04/38.48  tff(c_172403, plain, (![B_5620, C_5621, A_5622]: (k1_funct_1(k5_relat_1(B_5620, C_5621), A_5622)=k1_funct_1(C_5621, k1_funct_1(B_5620, A_5622)) | ~v1_funct_1(C_5621) | ~v1_relat_1(C_5621) | ~v1_funct_1(B_5620) | ~v1_relat_1(B_5620) | v1_xboole_0(k1_relat_1(B_5620)) | ~m1_subset_1(A_5622, k1_relat_1(B_5620)))), inference(resolution, [status(thm)], [c_10, c_168952])).
% 50.04/38.48  tff(c_172407, plain, (![C_5621, A_5622]: (k1_funct_1(k5_relat_1('#skF_5', C_5621), A_5622)=k1_funct_1(C_5621, k1_funct_1('#skF_5', A_5622)) | ~v1_funct_1(C_5621) | ~v1_relat_1(C_5621) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | v1_xboole_0(k1_relat_1('#skF_5')) | ~m1_subset_1(A_5622, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4435, c_172403])).
% 50.04/38.48  tff(c_172414, plain, (![C_5621, A_5622]: (k1_funct_1(k5_relat_1('#skF_5', C_5621), A_5622)=k1_funct_1(C_5621, k1_funct_1('#skF_5', A_5622)) | ~v1_funct_1(C_5621) | ~v1_relat_1(C_5621) | v1_xboole_0('#skF_3') | ~m1_subset_1(A_5622, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4435, c_119, c_66, c_172407])).
% 50.04/38.48  tff(c_178505, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_172414])).
% 50.04/38.48  tff(c_168799, plain, (![A_1]: (A_1='#skF_2' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_168778, c_2])).
% 50.04/38.48  tff(c_178508, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_178505, c_168799])).
% 50.04/38.48  tff(c_178512, plain, $false, inference(negUnitSimplification, [status(thm)], [c_168801, c_178508])).
% 50.04/38.48  tff(c_178513, plain, (![C_5621, A_5622]: (k1_funct_1(k5_relat_1('#skF_5', C_5621), A_5622)=k1_funct_1(C_5621, k1_funct_1('#skF_5', A_5622)) | ~v1_funct_1(C_5621) | ~v1_relat_1(C_5621) | ~m1_subset_1(A_5622, '#skF_3'))), inference(splitRight, [status(thm)], [c_172414])).
% 50.04/38.48  tff(c_168796, plain, (![A_7]: (r1_tarski('#skF_2', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_168778, c_97])).
% 50.04/38.48  tff(c_212, plain, (![A_84]: (v4_relat_1(k1_xboole_0, A_84))), inference(resolution, [status(thm)], [c_8, c_190])).
% 50.04/38.48  tff(c_168794, plain, (![A_84]: (v4_relat_1('#skF_2', A_84))), inference(demodulation, [status(thm), theory('equality')], [c_168778, c_212])).
% 50.04/38.48  tff(c_169458, plain, (![A_5466, A_5467, B_5468]: (r1_tarski(A_5466, A_5467) | ~r1_tarski(A_5466, k1_relat_1(B_5468)) | ~v4_relat_1(B_5468, A_5467) | ~v1_relat_1(B_5468))), inference(resolution, [status(thm)], [c_334, c_4])).
% 50.04/38.48  tff(c_169479, plain, (![A_5467]: (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), A_5467) | ~v4_relat_1('#skF_6', A_5467) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_617, c_169458])).
% 50.04/38.48  tff(c_169508, plain, (![A_5467]: (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), A_5467) | ~v4_relat_1('#skF_6', A_5467))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_169479])).
% 50.04/38.48  tff(c_170166, plain, (![A_5467]: (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), A_5467) | ~v4_relat_1('#skF_2', A_5467))), inference(demodulation, [status(thm), theory('equality')], [c_170158, c_169508])).
% 50.04/38.48  tff(c_170310, plain, (![A_5490]: (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), A_5490))), inference(demodulation, [status(thm), theory('equality')], [c_168794, c_170166])).
% 50.04/38.48  tff(c_170392, plain, (![A_5490]: (v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(A_5490, k2_relset_1('#skF_3', '#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_170310, c_130])).
% 50.04/38.48  tff(c_175814, plain, (![A_5713]: (~m1_subset_1(A_5713, k2_relset_1('#skF_3', '#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_170392])).
% 50.04/38.48  tff(c_175824, plain, $false, inference(resolution, [status(thm)], [c_6, c_175814])).
% 50.04/38.48  tff(c_175825, plain, (v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_170392])).
% 50.04/38.48  tff(c_175829, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_175825, c_168799])).
% 50.04/38.48  tff(c_169003, plain, (![C_5431, D_5432, A_5430, F_5433, E_5429, B_5434]: (k1_partfun1(A_5430, B_5434, C_5431, D_5432, E_5429, F_5433)=k5_relat_1(E_5429, F_5433) | ~m1_subset_1(F_5433, k1_zfmisc_1(k2_zfmisc_1(C_5431, D_5432))) | ~v1_funct_1(F_5433) | ~m1_subset_1(E_5429, k1_zfmisc_1(k2_zfmisc_1(A_5430, B_5434))) | ~v1_funct_1(E_5429))), inference(cnfTransformation, [status(thm)], [f_139])).
% 50.04/38.48  tff(c_172228, plain, (![A_5609, E_5608, D_5606, A_5607, B_5605, C_5604]: (k1_partfun1(A_5607, B_5605, C_5604, D_5606, E_5608, A_5609)=k5_relat_1(E_5608, A_5609) | ~v1_funct_1(A_5609) | ~m1_subset_1(E_5608, k1_zfmisc_1(k2_zfmisc_1(A_5607, B_5605))) | ~v1_funct_1(E_5608) | ~r1_tarski(A_5609, k2_zfmisc_1(C_5604, D_5606)))), inference(resolution, [status(thm)], [c_14, c_169003])).
% 50.04/38.48  tff(c_172236, plain, (![C_5604, D_5606, A_5609]: (k1_partfun1('#skF_3', '#skF_4', C_5604, D_5606, '#skF_5', A_5609)=k5_relat_1('#skF_5', A_5609) | ~v1_funct_1(A_5609) | ~v1_funct_1('#skF_5') | ~r1_tarski(A_5609, k2_zfmisc_1(C_5604, D_5606)))), inference(resolution, [status(thm)], [c_62, c_172228])).
% 50.04/38.48  tff(c_172269, plain, (![C_5612, D_5613, A_5614]: (k1_partfun1('#skF_3', '#skF_4', C_5612, D_5613, '#skF_5', A_5614)=k5_relat_1('#skF_5', A_5614) | ~v1_funct_1(A_5614) | ~r1_tarski(A_5614, k2_zfmisc_1(C_5612, D_5613)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_172236])).
% 50.04/38.48  tff(c_172315, plain, (![C_5612, D_5613]: (k1_partfun1('#skF_3', '#skF_4', C_5612, D_5613, '#skF_5', '#skF_2')=k5_relat_1('#skF_5', '#skF_2') | ~v1_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_168796, c_172269])).
% 50.04/38.48  tff(c_172347, plain, (![C_5612, D_5613]: (k1_partfun1('#skF_3', '#skF_4', C_5612, D_5613, '#skF_5', '#skF_2')=k5_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_170195, c_172315])).
% 50.04/38.48  tff(c_170159, plain, ('#skF_2'!='#skF_4'), inference(splitRight, [status(thm)], [c_170117])).
% 50.04/38.48  tff(c_610, plain, (![A_131, B_132]: (k1_relset_1(A_131, B_132, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_588])).
% 50.04/38.48  tff(c_758, plain, (![C_154, B_155]: (v1_funct_2(C_154, k1_xboole_0, B_155) | k1_relset_1(k1_xboole_0, B_155, C_154)!=k1_xboole_0 | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_155))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 50.04/38.48  tff(c_766, plain, (![B_155]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_155) | k1_relset_1(k1_xboole_0, B_155, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_758])).
% 50.04/38.48  tff(c_773, plain, (![B_155]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_155) | k1_relat_1(k1_xboole_0)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_610, c_766])).
% 50.04/38.48  tff(c_775, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_773])).
% 50.04/38.48  tff(c_3429, plain, (![B_338, B_339]: (r1_tarski(k1_relat_1(B_338), B_339) | ~v4_relat_1(B_338, '#skF_1'(k1_zfmisc_1(B_339))) | ~v1_relat_1(B_338))), inference(resolution, [status(thm)], [c_20, c_399])).
% 50.04/38.48  tff(c_3512, plain, (![B_339]: (r1_tarski(k1_relat_1(k1_xboole_0), B_339) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_212, c_3429])).
% 50.04/38.48  tff(c_3571, plain, (![B_340]: (r1_tarski(k1_relat_1(k1_xboole_0), B_340))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_3512])).
% 50.04/38.48  tff(c_3688, plain, (![B_340]: (v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~m1_subset_1(B_340, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_3571, c_130])).
% 50.04/38.48  tff(c_4143, plain, (![B_353]: (~m1_subset_1(B_353, k1_relat_1(k1_xboole_0)))), inference(splitLeft, [status(thm)], [c_3688])).
% 50.04/38.48  tff(c_4148, plain, $false, inference(resolution, [status(thm)], [c_6, c_4143])).
% 50.04/38.48  tff(c_4149, plain, (v1_xboole_0(k1_relat_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_3688])).
% 50.04/38.48  tff(c_4152, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_4149, c_2])).
% 50.04/38.48  tff(c_4156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_775, c_4152])).
% 50.04/38.48  tff(c_4158, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_773])).
% 50.04/38.48  tff(c_168788, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_168778, c_168778, c_4158])).
% 50.04/38.48  tff(c_169056, plain, (![E_5439, D_5443, C_5441, B_5440, A_5442]: (k1_partfun1(A_5442, B_5440, B_5440, C_5441, D_5443, E_5439)=k8_funct_2(A_5442, B_5440, C_5441, D_5443, E_5439) | B_5440='#skF_2' | ~r1_tarski(k2_relset_1(A_5442, B_5440, D_5443), k1_relset_1(B_5440, C_5441, E_5439)) | ~m1_subset_1(E_5439, k1_zfmisc_1(k2_zfmisc_1(B_5440, C_5441))) | ~v1_funct_1(E_5439) | ~m1_subset_1(D_5443, k1_zfmisc_1(k2_zfmisc_1(A_5442, B_5440))) | ~v1_funct_2(D_5443, A_5442, B_5440) | ~v1_funct_1(D_5443))), inference(demodulation, [status(thm), theory('equality')], [c_168778, c_34])).
% 50.04/38.48  tff(c_169065, plain, (![A_5442, D_5443]: (k1_partfun1(A_5442, '#skF_4', '#skF_4', '#skF_2', D_5443, '#skF_6')=k8_funct_2(A_5442, '#skF_4', '#skF_2', D_5443, '#skF_6') | '#skF_2'='#skF_4' | ~r1_tarski(k2_relset_1(A_5442, '#skF_4', D_5443), k1_relat_1('#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1(D_5443, k1_zfmisc_1(k2_zfmisc_1(A_5442, '#skF_4'))) | ~v1_funct_2(D_5443, A_5442, '#skF_4') | ~v1_funct_1(D_5443))), inference(superposition, [status(thm), theory('equality')], [c_609, c_169056])).
% 50.04/38.48  tff(c_169072, plain, (![A_5442, D_5443]: (k1_partfun1(A_5442, '#skF_4', '#skF_4', '#skF_2', D_5443, '#skF_6')=k8_funct_2(A_5442, '#skF_4', '#skF_2', D_5443, '#skF_6') | '#skF_2'='#skF_4' | ~r1_tarski(k2_relset_1(A_5442, '#skF_4', D_5443), k1_relat_1('#skF_6')) | ~m1_subset_1(D_5443, k1_zfmisc_1(k2_zfmisc_1(A_5442, '#skF_4'))) | ~v1_funct_2(D_5443, A_5442, '#skF_4') | ~v1_funct_1(D_5443))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_169065])).
% 50.04/38.48  tff(c_181961, plain, (![A_5442, D_5443]: (k1_partfun1(A_5442, '#skF_4', '#skF_4', '#skF_2', D_5443, '#skF_2')=k8_funct_2(A_5442, '#skF_4', '#skF_2', D_5443, '#skF_2') | '#skF_2'='#skF_4' | ~r1_tarski(k2_relset_1(A_5442, '#skF_4', D_5443), '#skF_2') | ~m1_subset_1(D_5443, k1_zfmisc_1(k2_zfmisc_1(A_5442, '#skF_4'))) | ~v1_funct_2(D_5443, A_5442, '#skF_4') | ~v1_funct_1(D_5443))), inference(demodulation, [status(thm), theory('equality')], [c_168788, c_170158, c_170158, c_170158, c_169072])).
% 50.04/38.48  tff(c_181963, plain, (![A_5928, D_5929]: (k1_partfun1(A_5928, '#skF_4', '#skF_4', '#skF_2', D_5929, '#skF_2')=k8_funct_2(A_5928, '#skF_4', '#skF_2', D_5929, '#skF_2') | ~r1_tarski(k2_relset_1(A_5928, '#skF_4', D_5929), '#skF_2') | ~m1_subset_1(D_5929, k1_zfmisc_1(k2_zfmisc_1(A_5928, '#skF_4'))) | ~v1_funct_2(D_5929, A_5928, '#skF_4') | ~v1_funct_1(D_5929))), inference(negUnitSimplification, [status(thm)], [c_170159, c_181961])).
% 50.04/38.48  tff(c_181978, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_2')=k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_2') | ~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_2') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_181963])).
% 50.04/38.48  tff(c_181990, plain, (k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_2')=k5_relat_1('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_168796, c_175829, c_172347, c_181978])).
% 50.04/38.48  tff(c_170190, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_2'), '#skF_7')!=k1_funct_1('#skF_2', k1_funct_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_170158, c_170158, c_50])).
% 50.04/38.48  tff(c_181992, plain, (k1_funct_1(k5_relat_1('#skF_5', '#skF_2'), '#skF_7')!=k1_funct_1('#skF_2', k1_funct_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_181990, c_170190])).
% 50.04/38.48  tff(c_181999, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_178513, c_181992])).
% 50.04/38.48  tff(c_182006, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_168797, c_170195, c_181999])).
% 50.04/38.48  tff(c_182007, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_168737])).
% 50.04/38.48  tff(c_182013, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_182007, c_617])).
% 50.04/38.48  tff(c_227543, plain, (![A_7168, B_7172, E_7167, F_7171, D_7170, C_7169]: (k1_partfun1(A_7168, B_7172, C_7169, D_7170, E_7167, F_7171)=k5_relat_1(E_7167, F_7171) | ~m1_subset_1(F_7171, k1_zfmisc_1(k2_zfmisc_1(C_7169, D_7170))) | ~v1_funct_1(F_7171) | ~m1_subset_1(E_7167, k1_zfmisc_1(k2_zfmisc_1(A_7168, B_7172))) | ~v1_funct_1(E_7167))), inference(cnfTransformation, [status(thm)], [f_139])).
% 50.04/38.48  tff(c_227550, plain, (![A_7168, B_7172, E_7167]: (k1_partfun1(A_7168, B_7172, '#skF_4', '#skF_2', E_7167, '#skF_6')=k5_relat_1(E_7167, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_7167, k1_zfmisc_1(k2_zfmisc_1(A_7168, B_7172))) | ~v1_funct_1(E_7167))), inference(resolution, [status(thm)], [c_58, c_227543])).
% 50.04/38.48  tff(c_228124, plain, (![A_7202, B_7203, E_7204]: (k1_partfun1(A_7202, B_7203, '#skF_4', '#skF_2', E_7204, '#skF_6')=k5_relat_1(E_7204, '#skF_6') | ~m1_subset_1(E_7204, k1_zfmisc_1(k2_zfmisc_1(A_7202, B_7203))) | ~v1_funct_1(E_7204))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_227550])).
% 50.04/38.48  tff(c_228131, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_228124])).
% 50.04/38.48  tff(c_228146, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_228131])).
% 50.04/38.48  tff(c_182030, plain, (![A_15]: (r1_tarski('#skF_4', A_15) | ~v4_relat_1('#skF_6', A_15) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_182007, c_20])).
% 50.04/38.48  tff(c_227478, plain, (![A_7165]: (r1_tarski('#skF_4', A_7165) | ~v4_relat_1('#skF_6', A_7165))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_182030])).
% 50.04/38.48  tff(c_227500, plain, (r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_211, c_227478])).
% 50.04/38.48  tff(c_182055, plain, (![B_5930, C_5931, A_5932]: (k1_xboole_0=B_5930 | v1_funct_2(C_5931, A_5932, B_5930) | k1_relset_1(A_5932, B_5930, C_5931)!=A_5932 | ~m1_subset_1(C_5931, k1_zfmisc_1(k2_zfmisc_1(A_5932, B_5930))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 50.04/38.48  tff(c_229248, plain, (![B_7253, A_7254, A_7255]: (k1_xboole_0=B_7253 | v1_funct_2(A_7254, A_7255, B_7253) | k1_relset_1(A_7255, B_7253, A_7254)!=A_7255 | ~r1_tarski(A_7254, k2_zfmisc_1(A_7255, B_7253)))), inference(resolution, [status(thm)], [c_14, c_182055])).
% 50.04/38.48  tff(c_229305, plain, (![A_97]: (k1_xboole_0='#skF_4' | v1_funct_2(A_97, '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', A_97)!='#skF_3' | ~r1_tarski(A_97, '#skF_5'))), inference(resolution, [status(thm)], [c_276, c_229248])).
% 50.04/38.48  tff(c_237317, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_229305])).
% 50.04/38.48  tff(c_182033, plain, (![A_15]: (v4_relat_1('#skF_6', A_15) | ~r1_tarski('#skF_4', A_15) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_182007, c_18])).
% 50.04/38.48  tff(c_182047, plain, (![A_15]: (v4_relat_1('#skF_6', A_15) | ~r1_tarski('#skF_4', A_15))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_182033])).
% 50.04/38.48  tff(c_358, plain, (![B_108, A_7]: (r1_tarski(k1_relat_1(B_108), A_7) | ~v4_relat_1(B_108, k1_xboole_0) | ~v1_relat_1(B_108))), inference(resolution, [status(thm)], [c_334, c_278])).
% 50.04/38.48  tff(c_182021, plain, (![A_7]: (r1_tarski('#skF_4', A_7) | ~v4_relat_1('#skF_6', k1_xboole_0) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_182007, c_358])).
% 50.04/38.48  tff(c_182039, plain, (![A_7]: (r1_tarski('#skF_4', A_7) | ~v4_relat_1('#skF_6', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_182021])).
% 50.04/38.48  tff(c_227630, plain, (~v4_relat_1('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_182039])).
% 50.04/38.48  tff(c_227634, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_182047, c_227630])).
% 50.04/38.48  tff(c_237348, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_237317, c_227634])).
% 50.04/38.48  tff(c_237380, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_227500, c_237348])).
% 50.04/38.48  tff(c_237382, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_229305])).
% 50.04/38.48  tff(c_182014, plain, (k1_relset_1('#skF_4', '#skF_2', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_182007, c_609])).
% 50.04/38.48  tff(c_227594, plain, (![D_7178, A_7177, B_7175, E_7174, C_7176]: (k1_partfun1(A_7177, B_7175, B_7175, C_7176, D_7178, E_7174)=k8_funct_2(A_7177, B_7175, C_7176, D_7178, E_7174) | k1_xboole_0=B_7175 | ~r1_tarski(k2_relset_1(A_7177, B_7175, D_7178), k1_relset_1(B_7175, C_7176, E_7174)) | ~m1_subset_1(E_7174, k1_zfmisc_1(k2_zfmisc_1(B_7175, C_7176))) | ~v1_funct_1(E_7174) | ~m1_subset_1(D_7178, k1_zfmisc_1(k2_zfmisc_1(A_7177, B_7175))) | ~v1_funct_2(D_7178, A_7177, B_7175) | ~v1_funct_1(D_7178))), inference(cnfTransformation, [status(thm)], [f_111])).
% 50.04/38.48  tff(c_227597, plain, (![A_7177, D_7178]: (k1_partfun1(A_7177, '#skF_4', '#skF_4', '#skF_2', D_7178, '#skF_6')=k8_funct_2(A_7177, '#skF_4', '#skF_2', D_7178, '#skF_6') | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relset_1(A_7177, '#skF_4', D_7178), '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1(D_7178, k1_zfmisc_1(k2_zfmisc_1(A_7177, '#skF_4'))) | ~v1_funct_2(D_7178, A_7177, '#skF_4') | ~v1_funct_1(D_7178))), inference(superposition, [status(thm), theory('equality')], [c_182014, c_227594])).
% 50.04/38.48  tff(c_227605, plain, (![A_7177, D_7178]: (k1_partfun1(A_7177, '#skF_4', '#skF_4', '#skF_2', D_7178, '#skF_6')=k8_funct_2(A_7177, '#skF_4', '#skF_2', D_7178, '#skF_6') | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relset_1(A_7177, '#skF_4', D_7178), '#skF_4') | ~m1_subset_1(D_7178, k1_zfmisc_1(k2_zfmisc_1(A_7177, '#skF_4'))) | ~v1_funct_2(D_7178, A_7177, '#skF_4') | ~v1_funct_1(D_7178))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_227597])).
% 50.04/38.48  tff(c_244282, plain, (![A_7685, D_7686]: (k1_partfun1(A_7685, '#skF_4', '#skF_4', '#skF_2', D_7686, '#skF_6')=k8_funct_2(A_7685, '#skF_4', '#skF_2', D_7686, '#skF_6') | ~r1_tarski(k2_relset_1(A_7685, '#skF_4', D_7686), '#skF_4') | ~m1_subset_1(D_7686, k1_zfmisc_1(k2_zfmisc_1(A_7685, '#skF_4'))) | ~v1_funct_2(D_7686, A_7685, '#skF_4') | ~v1_funct_1(D_7686))), inference(negUnitSimplification, [status(thm)], [c_237382, c_227605])).
% 50.04/38.48  tff(c_244293, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_244282])).
% 50.04/38.48  tff(c_244306, plain, (k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_182013, c_228146, c_244293])).
% 50.04/38.48  tff(c_244321, plain, (k1_funct_1(k5_relat_1('#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_244306, c_50])).
% 50.04/38.48  tff(c_244424, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_237314, c_244321])).
% 50.04/38.48  tff(c_244431, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_120, c_60, c_244424])).
% 50.04/38.48  tff(c_244439, plain, (![A_7688]: (r1_tarski('#skF_4', A_7688))), inference(splitRight, [status(thm)], [c_182039])).
% 50.04/38.48  tff(c_244467, plain, (![A_7688]: (v1_xboole_0('#skF_4') | ~m1_subset_1(A_7688, '#skF_4'))), inference(resolution, [status(thm)], [c_244439, c_130])).
% 50.04/38.48  tff(c_244488, plain, (![A_7689]: (~m1_subset_1(A_7689, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_244467])).
% 50.04/38.48  tff(c_244493, plain, $false, inference(resolution, [status(thm)], [c_6, c_244488])).
% 50.04/38.48  tff(c_244494, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_4380])).
% 50.04/38.48  tff(c_244512, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_244494, c_182])).
% 50.04/38.48  tff(c_244520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_244512])).
% 50.04/38.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 50.04/38.48  
% 50.04/38.48  Inference rules
% 50.04/38.48  ----------------------
% 50.04/38.48  #Ref     : 0
% 50.04/38.48  #Sup     : 48093
% 50.04/38.48  #Fact    : 0
% 50.04/38.48  #Define  : 0
% 50.04/38.48  #Split   : 683
% 50.04/38.48  #Chain   : 0
% 50.04/38.48  #Close   : 0
% 50.04/38.48  
% 50.04/38.48  Ordering : KBO
% 50.04/38.48  
% 50.04/38.48  Simplification rules
% 50.04/38.48  ----------------------
% 50.04/38.48  #Subsume      : 13506
% 50.04/38.48  #Demod        : 53621
% 50.04/38.48  #Tautology    : 14403
% 50.04/38.48  #SimpNegUnit  : 990
% 50.04/38.48  #BackRed      : 3874
% 50.04/38.48  
% 50.04/38.48  #Partial instantiations: 0
% 50.04/38.48  #Strategies tried      : 1
% 50.04/38.48  
% 50.04/38.48  Timing (in seconds)
% 50.04/38.48  ----------------------
% 50.04/38.48  Preprocessing        : 0.37
% 50.04/38.48  Parsing              : 0.19
% 50.04/38.48  CNF conversion       : 0.03
% 50.04/38.48  Main loop            : 37.22
% 50.04/38.48  Inferencing          : 7.20
% 50.04/38.48  Reduction            : 18.13
% 50.04/38.48  Demodulation         : 13.96
% 50.04/38.48  BG Simplification    : 0.58
% 50.04/38.48  Subsumption          : 9.13
% 50.04/38.48  Abstraction          : 1.13
% 50.04/38.48  MUC search           : 0.00
% 50.04/38.48  Cooper               : 0.00
% 50.04/38.48  Total                : 37.72
% 50.04/38.48  Index Insertion      : 0.00
% 50.04/38.48  Index Deletion       : 0.00
% 50.04/38.48  Index Matching       : 0.00
% 50.04/38.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
