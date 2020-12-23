%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:43 EST 2020

% Result     : Theorem 5.77s
% Output     : CNFRefutation 5.77s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 235 expanded)
%              Number of leaves         :   40 ( 100 expanded)
%              Depth                    :   10
%              Number of atoms          :  189 ( 823 expanded)
%              Number of equality atoms :   50 ( 214 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_148,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_113,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_123,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_95,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_2)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_46,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_85,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_102,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_85])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_54,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_3891,plain,(
    ! [A_799,B_800,C_801] :
      ( k1_relset_1(A_799,B_800,C_801) = k1_relat_1(C_801)
      | ~ m1_subset_1(C_801,k1_zfmisc_1(k2_zfmisc_1(A_799,B_800))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3907,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_3891])).

tff(c_4064,plain,(
    ! [B_829,A_830,C_831] :
      ( k1_xboole_0 = B_829
      | k1_relset_1(A_830,B_829,C_831) = A_830
      | ~ v1_funct_2(C_831,A_830,B_829)
      | ~ m1_subset_1(C_831,k1_zfmisc_1(k2_zfmisc_1(A_830,B_829))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4071,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_4064])).

tff(c_4082,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3907,c_4071])).

tff(c_4088,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4082])).

tff(c_101,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_85])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4089,plain,(
    ! [B_832,C_833,A_834] :
      ( k1_funct_1(k5_relat_1(B_832,C_833),A_834) = k1_funct_1(C_833,k1_funct_1(B_832,A_834))
      | ~ r2_hidden(A_834,k1_relat_1(B_832))
      | ~ v1_funct_1(C_833)
      | ~ v1_relat_1(C_833)
      | ~ v1_funct_1(B_832)
      | ~ v1_relat_1(B_832) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4146,plain,(
    ! [B_842,C_843,A_844] :
      ( k1_funct_1(k5_relat_1(B_842,C_843),A_844) = k1_funct_1(C_843,k1_funct_1(B_842,A_844))
      | ~ v1_funct_1(C_843)
      | ~ v1_relat_1(C_843)
      | ~ v1_funct_1(B_842)
      | ~ v1_relat_1(B_842)
      | v1_xboole_0(k1_relat_1(B_842))
      | ~ m1_subset_1(A_844,k1_relat_1(B_842)) ) ),
    inference(resolution,[status(thm)],[c_10,c_4089])).

tff(c_4148,plain,(
    ! [C_843,A_844] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_843),A_844) = k1_funct_1(C_843,k1_funct_1('#skF_4',A_844))
      | ~ v1_funct_1(C_843)
      | ~ v1_relat_1(C_843)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | v1_xboole_0(k1_relat_1('#skF_4'))
      | ~ m1_subset_1(A_844,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4088,c_4146])).

tff(c_4150,plain,(
    ! [C_843,A_844] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_843),A_844) = k1_funct_1(C_843,k1_funct_1('#skF_4',A_844))
      | ~ v1_funct_1(C_843)
      | ~ v1_relat_1(C_843)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_844,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4088,c_101,c_56,c_4148])).

tff(c_4151,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4150])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4173,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_4151,c_2])).

tff(c_4177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_4173])).

tff(c_4178,plain,(
    ! [C_843,A_844] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_843),A_844) = k1_funct_1(C_843,k1_funct_1('#skF_4',A_844))
      | ~ v1_funct_1(C_843)
      | ~ v1_relat_1(C_843)
      | ~ m1_subset_1(A_844,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_4150])).

tff(c_4197,plain,(
    ! [D_858,E_853,C_856,A_857,B_854,F_855] :
      ( k1_partfun1(A_857,B_854,C_856,D_858,E_853,F_855) = k5_relat_1(E_853,F_855)
      | ~ m1_subset_1(F_855,k1_zfmisc_1(k2_zfmisc_1(C_856,D_858)))
      | ~ v1_funct_1(F_855)
      | ~ m1_subset_1(E_853,k1_zfmisc_1(k2_zfmisc_1(A_857,B_854)))
      | ~ v1_funct_1(E_853) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_4204,plain,(
    ! [A_857,B_854,E_853] :
      ( k1_partfun1(A_857,B_854,'#skF_3','#skF_1',E_853,'#skF_5') = k5_relat_1(E_853,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_853,k1_zfmisc_1(k2_zfmisc_1(A_857,B_854)))
      | ~ v1_funct_1(E_853) ) ),
    inference(resolution,[status(thm)],[c_48,c_4197])).

tff(c_4283,plain,(
    ! [A_870,B_871,E_872] :
      ( k1_partfun1(A_870,B_871,'#skF_3','#skF_1',E_872,'#skF_5') = k5_relat_1(E_872,'#skF_5')
      | ~ m1_subset_1(E_872,k1_zfmisc_1(k2_zfmisc_1(A_870,B_871)))
      | ~ v1_funct_1(E_872) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_4204])).

tff(c_4290,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_4283])).

tff(c_4301,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_4290])).

tff(c_3908,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_3891])).

tff(c_44,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_3915,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3908,c_44])).

tff(c_4248,plain,(
    ! [D_865,E_863,C_862,A_866,B_864] :
      ( k1_partfun1(A_866,B_864,B_864,C_862,D_865,E_863) = k8_funct_2(A_866,B_864,C_862,D_865,E_863)
      | k1_xboole_0 = B_864
      | ~ r1_tarski(k2_relset_1(A_866,B_864,D_865),k1_relset_1(B_864,C_862,E_863))
      | ~ m1_subset_1(E_863,k1_zfmisc_1(k2_zfmisc_1(B_864,C_862)))
      | ~ v1_funct_1(E_863)
      | ~ m1_subset_1(D_865,k1_zfmisc_1(k2_zfmisc_1(A_866,B_864)))
      | ~ v1_funct_2(D_865,A_866,B_864)
      | ~ v1_funct_1(D_865) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_4257,plain,(
    ! [A_866,D_865] :
      ( k1_partfun1(A_866,'#skF_3','#skF_3','#skF_1',D_865,'#skF_5') = k8_funct_2(A_866,'#skF_3','#skF_1',D_865,'#skF_5')
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relset_1(A_866,'#skF_3',D_865),k1_relat_1('#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_865,k1_zfmisc_1(k2_zfmisc_1(A_866,'#skF_3')))
      | ~ v1_funct_2(D_865,A_866,'#skF_3')
      | ~ v1_funct_1(D_865) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3908,c_4248])).

tff(c_4264,plain,(
    ! [A_866,D_865] :
      ( k1_partfun1(A_866,'#skF_3','#skF_3','#skF_1',D_865,'#skF_5') = k8_funct_2(A_866,'#skF_3','#skF_1',D_865,'#skF_5')
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relset_1(A_866,'#skF_3',D_865),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_865,k1_zfmisc_1(k2_zfmisc_1(A_866,'#skF_3')))
      | ~ v1_funct_2(D_865,A_866,'#skF_3')
      | ~ v1_funct_1(D_865) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_4257])).

tff(c_4414,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4264])).

tff(c_8,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_66,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_82,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_8,c_66])).

tff(c_4,plain,(
    ! [A_2] : r1_xboole_0(A_2,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_121,plain,(
    ! [B_66,A_67] :
      ( ~ r1_xboole_0(B_66,A_67)
      | ~ r1_tarski(B_66,A_67)
      | v1_xboole_0(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_139,plain,(
    ! [A_71] :
      ( ~ r1_tarski(A_71,k1_xboole_0)
      | v1_xboole_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_4,c_121])).

tff(c_144,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_82,c_139])).

tff(c_4433,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4414,c_144])).

tff(c_4443,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4433])).

tff(c_4446,plain,(
    ! [A_898,D_899] :
      ( k1_partfun1(A_898,'#skF_3','#skF_3','#skF_1',D_899,'#skF_5') = k8_funct_2(A_898,'#skF_3','#skF_1',D_899,'#skF_5')
      | ~ r1_tarski(k2_relset_1(A_898,'#skF_3',D_899),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_899,k1_zfmisc_1(k2_zfmisc_1(A_898,'#skF_3')))
      | ~ v1_funct_2(D_899,A_898,'#skF_3')
      | ~ v1_funct_1(D_899) ) ),
    inference(splitRight,[status(thm)],[c_4264])).

tff(c_4449,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3915,c_4446])).

tff(c_4452,plain,(
    k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_4301,c_4449])).

tff(c_40,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_4453,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4452,c_40])).

tff(c_4460,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4178,c_4453])).

tff(c_4467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_102,c_50,c_4460])).

tff(c_4468,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4082])).

tff(c_4484,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4468,c_144])).

tff(c_4494,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4484])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.77/2.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.77/2.13  
% 5.77/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.77/2.13  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.77/2.13  
% 5.77/2.13  %Foreground sorts:
% 5.77/2.13  
% 5.77/2.13  
% 5.77/2.13  %Background operators:
% 5.77/2.13  
% 5.77/2.13  
% 5.77/2.13  %Foreground operators:
% 5.77/2.13  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.77/2.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.77/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.77/2.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.77/2.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.77/2.13  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.77/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.77/2.13  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.77/2.13  tff('#skF_5', type, '#skF_5': $i).
% 5.77/2.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.77/2.13  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 5.77/2.13  tff('#skF_6', type, '#skF_6': $i).
% 5.77/2.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.77/2.13  tff('#skF_2', type, '#skF_2': $i).
% 5.77/2.13  tff('#skF_3', type, '#skF_3': $i).
% 5.77/2.13  tff('#skF_1', type, '#skF_1': $i).
% 5.77/2.13  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.77/2.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.77/2.13  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.77/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.77/2.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.77/2.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.77/2.13  tff('#skF_4', type, '#skF_4': $i).
% 5.77/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.77/2.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.77/2.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.77/2.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.77/2.13  
% 5.77/2.15  tff(f_148, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 5.77/2.15  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.77/2.15  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.77/2.15  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.77/2.15  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 5.77/2.15  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 5.77/2.15  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.77/2.15  tff(f_123, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.77/2.15  tff(f_95, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_2)).
% 5.77/2.15  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.77/2.15  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.77/2.15  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.77/2.15  tff(f_39, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 5.77/2.15  tff(c_58, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.77/2.15  tff(c_46, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.77/2.15  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.77/2.15  tff(c_85, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.77/2.15  tff(c_102, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_85])).
% 5.77/2.15  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.77/2.15  tff(c_42, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.77/2.15  tff(c_54, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.77/2.15  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.77/2.15  tff(c_3891, plain, (![A_799, B_800, C_801]: (k1_relset_1(A_799, B_800, C_801)=k1_relat_1(C_801) | ~m1_subset_1(C_801, k1_zfmisc_1(k2_zfmisc_1(A_799, B_800))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.77/2.15  tff(c_3907, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_3891])).
% 5.77/2.15  tff(c_4064, plain, (![B_829, A_830, C_831]: (k1_xboole_0=B_829 | k1_relset_1(A_830, B_829, C_831)=A_830 | ~v1_funct_2(C_831, A_830, B_829) | ~m1_subset_1(C_831, k1_zfmisc_1(k2_zfmisc_1(A_830, B_829))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.77/2.15  tff(c_4071, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_4064])).
% 5.77/2.15  tff(c_4082, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3907, c_4071])).
% 5.77/2.15  tff(c_4088, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_4082])).
% 5.77/2.15  tff(c_101, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_85])).
% 5.77/2.15  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.77/2.15  tff(c_10, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.77/2.15  tff(c_4089, plain, (![B_832, C_833, A_834]: (k1_funct_1(k5_relat_1(B_832, C_833), A_834)=k1_funct_1(C_833, k1_funct_1(B_832, A_834)) | ~r2_hidden(A_834, k1_relat_1(B_832)) | ~v1_funct_1(C_833) | ~v1_relat_1(C_833) | ~v1_funct_1(B_832) | ~v1_relat_1(B_832))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.77/2.15  tff(c_4146, plain, (![B_842, C_843, A_844]: (k1_funct_1(k5_relat_1(B_842, C_843), A_844)=k1_funct_1(C_843, k1_funct_1(B_842, A_844)) | ~v1_funct_1(C_843) | ~v1_relat_1(C_843) | ~v1_funct_1(B_842) | ~v1_relat_1(B_842) | v1_xboole_0(k1_relat_1(B_842)) | ~m1_subset_1(A_844, k1_relat_1(B_842)))), inference(resolution, [status(thm)], [c_10, c_4089])).
% 5.77/2.15  tff(c_4148, plain, (![C_843, A_844]: (k1_funct_1(k5_relat_1('#skF_4', C_843), A_844)=k1_funct_1(C_843, k1_funct_1('#skF_4', A_844)) | ~v1_funct_1(C_843) | ~v1_relat_1(C_843) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | v1_xboole_0(k1_relat_1('#skF_4')) | ~m1_subset_1(A_844, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4088, c_4146])).
% 5.77/2.15  tff(c_4150, plain, (![C_843, A_844]: (k1_funct_1(k5_relat_1('#skF_4', C_843), A_844)=k1_funct_1(C_843, k1_funct_1('#skF_4', A_844)) | ~v1_funct_1(C_843) | ~v1_relat_1(C_843) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_844, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4088, c_101, c_56, c_4148])).
% 5.77/2.15  tff(c_4151, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_4150])).
% 5.77/2.15  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.77/2.15  tff(c_4173, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_4151, c_2])).
% 5.77/2.15  tff(c_4177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_4173])).
% 5.77/2.15  tff(c_4178, plain, (![C_843, A_844]: (k1_funct_1(k5_relat_1('#skF_4', C_843), A_844)=k1_funct_1(C_843, k1_funct_1('#skF_4', A_844)) | ~v1_funct_1(C_843) | ~v1_relat_1(C_843) | ~m1_subset_1(A_844, '#skF_2'))), inference(splitRight, [status(thm)], [c_4150])).
% 5.77/2.15  tff(c_4197, plain, (![D_858, E_853, C_856, A_857, B_854, F_855]: (k1_partfun1(A_857, B_854, C_856, D_858, E_853, F_855)=k5_relat_1(E_853, F_855) | ~m1_subset_1(F_855, k1_zfmisc_1(k2_zfmisc_1(C_856, D_858))) | ~v1_funct_1(F_855) | ~m1_subset_1(E_853, k1_zfmisc_1(k2_zfmisc_1(A_857, B_854))) | ~v1_funct_1(E_853))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.77/2.15  tff(c_4204, plain, (![A_857, B_854, E_853]: (k1_partfun1(A_857, B_854, '#skF_3', '#skF_1', E_853, '#skF_5')=k5_relat_1(E_853, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_853, k1_zfmisc_1(k2_zfmisc_1(A_857, B_854))) | ~v1_funct_1(E_853))), inference(resolution, [status(thm)], [c_48, c_4197])).
% 5.77/2.15  tff(c_4283, plain, (![A_870, B_871, E_872]: (k1_partfun1(A_870, B_871, '#skF_3', '#skF_1', E_872, '#skF_5')=k5_relat_1(E_872, '#skF_5') | ~m1_subset_1(E_872, k1_zfmisc_1(k2_zfmisc_1(A_870, B_871))) | ~v1_funct_1(E_872))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_4204])).
% 5.77/2.15  tff(c_4290, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_4283])).
% 5.77/2.15  tff(c_4301, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_4290])).
% 5.77/2.15  tff(c_3908, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_3891])).
% 5.77/2.15  tff(c_44, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.77/2.15  tff(c_3915, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3908, c_44])).
% 5.77/2.15  tff(c_4248, plain, (![D_865, E_863, C_862, A_866, B_864]: (k1_partfun1(A_866, B_864, B_864, C_862, D_865, E_863)=k8_funct_2(A_866, B_864, C_862, D_865, E_863) | k1_xboole_0=B_864 | ~r1_tarski(k2_relset_1(A_866, B_864, D_865), k1_relset_1(B_864, C_862, E_863)) | ~m1_subset_1(E_863, k1_zfmisc_1(k2_zfmisc_1(B_864, C_862))) | ~v1_funct_1(E_863) | ~m1_subset_1(D_865, k1_zfmisc_1(k2_zfmisc_1(A_866, B_864))) | ~v1_funct_2(D_865, A_866, B_864) | ~v1_funct_1(D_865))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.77/2.15  tff(c_4257, plain, (![A_866, D_865]: (k1_partfun1(A_866, '#skF_3', '#skF_3', '#skF_1', D_865, '#skF_5')=k8_funct_2(A_866, '#skF_3', '#skF_1', D_865, '#skF_5') | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relset_1(A_866, '#skF_3', D_865), k1_relat_1('#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_865, k1_zfmisc_1(k2_zfmisc_1(A_866, '#skF_3'))) | ~v1_funct_2(D_865, A_866, '#skF_3') | ~v1_funct_1(D_865))), inference(superposition, [status(thm), theory('equality')], [c_3908, c_4248])).
% 5.77/2.15  tff(c_4264, plain, (![A_866, D_865]: (k1_partfun1(A_866, '#skF_3', '#skF_3', '#skF_1', D_865, '#skF_5')=k8_funct_2(A_866, '#skF_3', '#skF_1', D_865, '#skF_5') | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relset_1(A_866, '#skF_3', D_865), k1_relat_1('#skF_5')) | ~m1_subset_1(D_865, k1_zfmisc_1(k2_zfmisc_1(A_866, '#skF_3'))) | ~v1_funct_2(D_865, A_866, '#skF_3') | ~v1_funct_1(D_865))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_4257])).
% 5.77/2.15  tff(c_4414, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_4264])).
% 5.77/2.15  tff(c_8, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.77/2.15  tff(c_66, plain, (![A_55, B_56]: (r1_tarski(A_55, B_56) | ~m1_subset_1(A_55, k1_zfmisc_1(B_56)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.77/2.15  tff(c_82, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_8, c_66])).
% 5.77/2.15  tff(c_4, plain, (![A_2]: (r1_xboole_0(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.77/2.15  tff(c_121, plain, (![B_66, A_67]: (~r1_xboole_0(B_66, A_67) | ~r1_tarski(B_66, A_67) | v1_xboole_0(B_66))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.77/2.15  tff(c_139, plain, (![A_71]: (~r1_tarski(A_71, k1_xboole_0) | v1_xboole_0(A_71))), inference(resolution, [status(thm)], [c_4, c_121])).
% 5.77/2.15  tff(c_144, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_82, c_139])).
% 5.77/2.15  tff(c_4433, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4414, c_144])).
% 5.77/2.15  tff(c_4443, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_4433])).
% 5.77/2.15  tff(c_4446, plain, (![A_898, D_899]: (k1_partfun1(A_898, '#skF_3', '#skF_3', '#skF_1', D_899, '#skF_5')=k8_funct_2(A_898, '#skF_3', '#skF_1', D_899, '#skF_5') | ~r1_tarski(k2_relset_1(A_898, '#skF_3', D_899), k1_relat_1('#skF_5')) | ~m1_subset_1(D_899, k1_zfmisc_1(k2_zfmisc_1(A_898, '#skF_3'))) | ~v1_funct_2(D_899, A_898, '#skF_3') | ~v1_funct_1(D_899))), inference(splitRight, [status(thm)], [c_4264])).
% 5.77/2.15  tff(c_4449, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_3915, c_4446])).
% 5.77/2.15  tff(c_4452, plain, (k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_4301, c_4449])).
% 5.77/2.15  tff(c_40, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.77/2.15  tff(c_4453, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4452, c_40])).
% 5.77/2.15  tff(c_4460, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4178, c_4453])).
% 5.77/2.15  tff(c_4467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_102, c_50, c_4460])).
% 5.77/2.15  tff(c_4468, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_4082])).
% 5.77/2.15  tff(c_4484, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4468, c_144])).
% 5.77/2.15  tff(c_4494, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_4484])).
% 5.77/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.77/2.15  
% 5.77/2.15  Inference rules
% 5.77/2.15  ----------------------
% 5.77/2.15  #Ref     : 0
% 5.77/2.15  #Sup     : 756
% 5.77/2.15  #Fact    : 0
% 5.77/2.15  #Define  : 0
% 5.77/2.15  #Split   : 49
% 5.77/2.15  #Chain   : 0
% 5.77/2.15  #Close   : 0
% 5.77/2.15  
% 5.77/2.15  Ordering : KBO
% 5.77/2.15  
% 5.77/2.15  Simplification rules
% 5.77/2.15  ----------------------
% 5.77/2.15  #Subsume      : 108
% 5.77/2.15  #Demod        : 1239
% 5.77/2.15  #Tautology    : 390
% 5.77/2.15  #SimpNegUnit  : 58
% 5.77/2.15  #BackRed      : 396
% 5.77/2.15  
% 5.77/2.15  #Partial instantiations: 0
% 5.77/2.15  #Strategies tried      : 1
% 5.77/2.15  
% 5.77/2.15  Timing (in seconds)
% 5.77/2.15  ----------------------
% 5.77/2.15  Preprocessing        : 0.35
% 5.77/2.15  Parsing              : 0.18
% 5.77/2.15  CNF conversion       : 0.03
% 5.77/2.15  Main loop            : 1.03
% 5.77/2.15  Inferencing          : 0.37
% 5.77/2.15  Reduction            : 0.35
% 5.77/2.15  Demodulation         : 0.23
% 5.77/2.15  BG Simplification    : 0.05
% 5.77/2.15  Subsumption          : 0.18
% 5.92/2.15  Abstraction          : 0.05
% 5.92/2.15  MUC search           : 0.00
% 5.92/2.15  Cooper               : 0.00
% 5.92/2.15  Total                : 1.42
% 5.92/2.15  Index Insertion      : 0.00
% 5.92/2.15  Index Deletion       : 0.00
% 5.92/2.15  Index Matching       : 0.00
% 5.92/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
