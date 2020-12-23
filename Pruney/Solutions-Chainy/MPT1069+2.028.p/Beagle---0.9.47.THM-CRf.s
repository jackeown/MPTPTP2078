%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:49 EST 2020

% Result     : Theorem 27.30s
% Output     : CNFRefutation 27.44s
% Verified   : 
% Statistics : Number of formulae       :  201 ( 824 expanded)
%              Number of leaves         :   48 ( 304 expanded)
%              Depth                    :   15
%              Number of atoms          :  515 (2897 expanded)
%              Number of equality atoms :  117 ( 673 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_192,negated_conjecture,(
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
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k7_partfun1(A,E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_167,axiom,(
    ! [A,B,C] :
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

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_106,axiom,(
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

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_143,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_130,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => m1_subset_1(k3_funct_2(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_80,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_68,plain,(
    m1_subset_1('#skF_8','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_78,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_76,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_74,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_70,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_447,plain,(
    ! [A_144,B_145,C_146] :
      ( k1_relset_1(A_144,B_145,C_146) = k1_relat_1(C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_460,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_447])).

tff(c_349,plain,(
    ! [A_135,B_136,C_137] :
      ( k2_relset_1(A_135,B_136,C_137) = k2_relat_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_361,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_349])).

tff(c_66,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_363,plain,(
    r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_66])).

tff(c_507,plain,(
    r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_363])).

tff(c_72,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_32233,plain,(
    ! [F_2057,D_2053,A_2055,B_2054,E_2058,C_2056] :
      ( k1_funct_1(k8_funct_2(B_2054,C_2056,A_2055,D_2053,E_2058),F_2057) = k1_funct_1(E_2058,k1_funct_1(D_2053,F_2057))
      | k1_xboole_0 = B_2054
      | ~ r1_tarski(k2_relset_1(B_2054,C_2056,D_2053),k1_relset_1(C_2056,A_2055,E_2058))
      | ~ m1_subset_1(F_2057,B_2054)
      | ~ m1_subset_1(E_2058,k1_zfmisc_1(k2_zfmisc_1(C_2056,A_2055)))
      | ~ v1_funct_1(E_2058)
      | ~ m1_subset_1(D_2053,k1_zfmisc_1(k2_zfmisc_1(B_2054,C_2056)))
      | ~ v1_funct_2(D_2053,B_2054,C_2056)
      | ~ v1_funct_1(D_2053)
      | v1_xboole_0(C_2056) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_32245,plain,(
    ! [B_2054,D_2053,F_2057] :
      ( k1_funct_1(k8_funct_2(B_2054,'#skF_5','#skF_3',D_2053,'#skF_7'),F_2057) = k1_funct_1('#skF_7',k1_funct_1(D_2053,F_2057))
      | k1_xboole_0 = B_2054
      | ~ r1_tarski(k2_relset_1(B_2054,'#skF_5',D_2053),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_2057,B_2054)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_2053,k1_zfmisc_1(k2_zfmisc_1(B_2054,'#skF_5')))
      | ~ v1_funct_2(D_2053,B_2054,'#skF_5')
      | ~ v1_funct_1(D_2053)
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_32233])).

tff(c_32257,plain,(
    ! [B_2054,D_2053,F_2057] :
      ( k1_funct_1(k8_funct_2(B_2054,'#skF_5','#skF_3',D_2053,'#skF_7'),F_2057) = k1_funct_1('#skF_7',k1_funct_1(D_2053,F_2057))
      | k1_xboole_0 = B_2054
      | ~ r1_tarski(k2_relset_1(B_2054,'#skF_5',D_2053),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_2057,B_2054)
      | ~ m1_subset_1(D_2053,k1_zfmisc_1(k2_zfmisc_1(B_2054,'#skF_5')))
      | ~ v1_funct_2(D_2053,B_2054,'#skF_5')
      | ~ v1_funct_1(D_2053)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_32245])).

tff(c_77144,plain,(
    ! [B_3197,D_3198,F_3199] :
      ( k1_funct_1(k8_funct_2(B_3197,'#skF_5','#skF_3',D_3198,'#skF_7'),F_3199) = k1_funct_1('#skF_7',k1_funct_1(D_3198,F_3199))
      | k1_xboole_0 = B_3197
      | ~ r1_tarski(k2_relset_1(B_3197,'#skF_5',D_3198),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_3199,B_3197)
      | ~ m1_subset_1(D_3198,k1_zfmisc_1(k2_zfmisc_1(B_3197,'#skF_5')))
      | ~ v1_funct_2(D_3198,B_3197,'#skF_5')
      | ~ v1_funct_1(D_3198) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_32257])).

tff(c_77152,plain,(
    ! [F_3199] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_3199) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_3199))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_3199,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_77144])).

tff(c_77157,plain,(
    ! [F_3199] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_3199) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_3199))
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(F_3199,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_507,c_77152])).

tff(c_77158,plain,(
    ! [F_3199] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_3199) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_3199))
      | ~ m1_subset_1(F_3199,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_77157])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_195,plain,(
    ! [C_101,A_102,B_103] :
      ( v1_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_207,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_195])).

tff(c_459,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_447])).

tff(c_31524,plain,(
    ! [B_1983,A_1984,C_1985] :
      ( k1_xboole_0 = B_1983
      | k1_relset_1(A_1984,B_1983,C_1985) = A_1984
      | ~ v1_funct_2(C_1985,A_1984,B_1983)
      | ~ m1_subset_1(C_1985,k1_zfmisc_1(k2_zfmisc_1(A_1984,B_1983))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_31531,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_31524])).

tff(c_31538,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_459,c_31531])).

tff(c_31541,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_31538])).

tff(c_26,plain,(
    ! [B_18,A_17] :
      ( v4_relat_1(B_18,A_17)
      | ~ r1_tarski(k1_relat_1(B_18),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_31557,plain,(
    ! [A_17] :
      ( v4_relat_1('#skF_6',A_17)
      | ~ r1_tarski('#skF_4',A_17)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31541,c_26])).

tff(c_31573,plain,(
    ! [A_17] :
      ( v4_relat_1('#skF_6',A_17)
      | ~ r1_tarski('#skF_4',A_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_31557])).

tff(c_335,plain,(
    ! [C_132,A_133,B_134] :
      ( v4_relat_1(C_132,A_133)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_347,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_335])).

tff(c_290,plain,(
    ! [B_119,A_120] :
      ( r1_tarski(k1_relat_1(B_119),A_120)
      | ~ v4_relat_1(B_119,A_120)
      | ~ v1_relat_1(B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_104,plain,(
    ! [A_85,B_86] :
      ( r2_hidden('#skF_2'(A_85,B_86),A_85)
      | r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_108,plain,(
    ! [A_85,B_86] :
      ( ~ v1_xboole_0(A_85)
      | r1_tarski(A_85,B_86) ) ),
    inference(resolution,[status(thm)],[c_104,c_2])).

tff(c_110,plain,(
    ! [B_89,A_90] :
      ( B_89 = A_90
      | ~ r1_tarski(B_89,A_90)
      | ~ r1_tarski(A_90,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_121,plain,(
    ! [B_86,A_85] :
      ( B_86 = A_85
      | ~ r1_tarski(B_86,A_85)
      | ~ v1_xboole_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_108,c_110])).

tff(c_31176,plain,(
    ! [B_1956,A_1957] :
      ( k1_relat_1(B_1956) = A_1957
      | ~ v1_xboole_0(A_1957)
      | ~ v4_relat_1(B_1956,A_1957)
      | ~ v1_relat_1(B_1956) ) ),
    inference(resolution,[status(thm)],[c_290,c_121])).

tff(c_31194,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_xboole_0('#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_347,c_31176])).

tff(c_31213,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_31194])).

tff(c_31216,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_31213])).

tff(c_28,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k1_relat_1(B_18),A_17)
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | v1_xboole_0(B_14)
      | ~ m1_subset_1(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_238,plain,(
    ! [C_110,B_111,A_112] :
      ( r2_hidden(C_110,B_111)
      | ~ r2_hidden(C_110,A_112)
      | ~ r1_tarski(A_112,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_31703,plain,(
    ! [A_1995,B_1996,B_1997] :
      ( r2_hidden(A_1995,B_1996)
      | ~ r1_tarski(B_1997,B_1996)
      | v1_xboole_0(B_1997)
      | ~ m1_subset_1(A_1995,B_1997) ) ),
    inference(resolution,[status(thm)],[c_20,c_238])).

tff(c_85301,plain,(
    ! [A_3490,A_3491,B_3492] :
      ( r2_hidden(A_3490,A_3491)
      | v1_xboole_0(k1_relat_1(B_3492))
      | ~ m1_subset_1(A_3490,k1_relat_1(B_3492))
      | ~ v4_relat_1(B_3492,A_3491)
      | ~ v1_relat_1(B_3492) ) ),
    inference(resolution,[status(thm)],[c_28,c_31703])).

tff(c_85309,plain,(
    ! [A_3490,A_3491] :
      ( r2_hidden(A_3490,A_3491)
      | v1_xboole_0(k1_relat_1('#skF_6'))
      | ~ m1_subset_1(A_3490,'#skF_4')
      | ~ v4_relat_1('#skF_6',A_3491)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31541,c_85301])).

tff(c_85319,plain,(
    ! [A_3490,A_3491] :
      ( r2_hidden(A_3490,A_3491)
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_3490,'#skF_4')
      | ~ v4_relat_1('#skF_6',A_3491) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_31541,c_85309])).

tff(c_89094,plain,(
    ! [A_3602,A_3603] :
      ( r2_hidden(A_3602,A_3603)
      | ~ m1_subset_1(A_3602,'#skF_4')
      | ~ v4_relat_1('#skF_6',A_3603) ) ),
    inference(negUnitSimplification,[status(thm)],[c_31216,c_85319])).

tff(c_89131,plain,(
    ! [A_3602,A_17] :
      ( r2_hidden(A_3602,A_17)
      | ~ m1_subset_1(A_3602,'#skF_4')
      | ~ r1_tarski('#skF_4',A_17) ) ),
    inference(resolution,[status(thm)],[c_31573,c_89094])).

tff(c_250,plain,(
    ! [C_113,B_114,A_115] :
      ( v5_relat_1(C_113,B_114)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_115,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_263,plain,(
    v5_relat_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_250])).

tff(c_208,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_195])).

tff(c_31217,plain,(
    ! [B_1958,A_1959] :
      ( r2_hidden(k1_funct_1(B_1958,A_1959),k2_relat_1(B_1958))
      | ~ r2_hidden(A_1959,k1_relat_1(B_1958))
      | ~ v1_funct_1(B_1958)
      | ~ v1_relat_1(B_1958) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_77643,plain,(
    ! [B_3233,A_3234,B_3235] :
      ( r2_hidden(k1_funct_1(B_3233,A_3234),B_3235)
      | ~ r1_tarski(k2_relat_1(B_3233),B_3235)
      | ~ r2_hidden(A_3234,k1_relat_1(B_3233))
      | ~ v1_funct_1(B_3233)
      | ~ v1_relat_1(B_3233) ) ),
    inference(resolution,[status(thm)],[c_31217,c_6])).

tff(c_54,plain,(
    ! [A_36,B_37,C_39] :
      ( k7_partfun1(A_36,B_37,C_39) = k1_funct_1(B_37,C_39)
      | ~ r2_hidden(C_39,k1_relat_1(B_37))
      | ~ v1_funct_1(B_37)
      | ~ v5_relat_1(B_37,A_36)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_90572,plain,(
    ! [A_3634,B_3635,B_3636,A_3637] :
      ( k7_partfun1(A_3634,B_3635,k1_funct_1(B_3636,A_3637)) = k1_funct_1(B_3635,k1_funct_1(B_3636,A_3637))
      | ~ v1_funct_1(B_3635)
      | ~ v5_relat_1(B_3635,A_3634)
      | ~ v1_relat_1(B_3635)
      | ~ r1_tarski(k2_relat_1(B_3636),k1_relat_1(B_3635))
      | ~ r2_hidden(A_3637,k1_relat_1(B_3636))
      | ~ v1_funct_1(B_3636)
      | ~ v1_relat_1(B_3636) ) ),
    inference(resolution,[status(thm)],[c_77643,c_54])).

tff(c_90598,plain,(
    ! [A_3634,A_3637] :
      ( k7_partfun1(A_3634,'#skF_7',k1_funct_1('#skF_6',A_3637)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_3637))
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_3634)
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(A_3637,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_507,c_90572])).

tff(c_101653,plain,(
    ! [A_3874,A_3875] :
      ( k7_partfun1(A_3874,'#skF_7',k1_funct_1('#skF_6',A_3875)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_3875))
      | ~ v5_relat_1('#skF_7',A_3874)
      | ~ r2_hidden(A_3875,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_78,c_31541,c_208,c_72,c_90598])).

tff(c_62,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) != k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_101659,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ v5_relat_1('#skF_7','#skF_3')
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_101653,c_62])).

tff(c_101665,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_101659])).

tff(c_101774,plain,(
    ~ r2_hidden('#skF_8','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_101665])).

tff(c_101777,plain,
    ( ~ m1_subset_1('#skF_8','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_89131,c_101774])).

tff(c_101787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_68,c_101777])).

tff(c_101788,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_101665])).

tff(c_102217,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_77158,c_101788])).

tff(c_102221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_102217])).

tff(c_102222,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_31538])).

tff(c_986,plain,(
    ! [B_246,C_247,A_248] :
      ( k1_xboole_0 = B_246
      | v1_funct_2(C_247,A_248,B_246)
      | k1_relset_1(A_248,B_246,C_247) != A_248
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_248,B_246))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_996,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_7','#skF_5','#skF_3')
    | k1_relset_1('#skF_5','#skF_3','#skF_7') != '#skF_5' ),
    inference(resolution,[status(thm)],[c_70,c_986])).

tff(c_1001,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_7','#skF_5','#skF_3')
    | k1_relat_1('#skF_7') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_996])).

tff(c_1002,plain,(
    k1_relat_1('#skF_7') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1001])).

tff(c_348,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_335])).

tff(c_18,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_530,plain,(
    ! [A_155,B_156] :
      ( r2_hidden('#skF_1'(A_155),B_156)
      | ~ r1_tarski(A_155,B_156)
      | v1_xboole_0(A_155) ) ),
    inference(resolution,[status(thm)],[c_4,c_238])).

tff(c_538,plain,(
    ! [B_157,A_158] :
      ( ~ v1_xboole_0(B_157)
      | ~ r1_tarski(A_158,B_157)
      | v1_xboole_0(A_158) ) ),
    inference(resolution,[status(thm)],[c_530,c_2])).

tff(c_566,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(A_12)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_538])).

tff(c_582,plain,(
    ! [A_12] : ~ v1_xboole_0(A_12) ),
    inference(splitLeft,[status(thm)],[c_566])).

tff(c_60,plain,(
    ! [B_49,F_64,E_62,A_48,C_50,D_58] :
      ( k1_funct_1(k8_funct_2(B_49,C_50,A_48,D_58,E_62),F_64) = k1_funct_1(E_62,k1_funct_1(D_58,F_64))
      | k1_xboole_0 = B_49
      | ~ r1_tarski(k2_relset_1(B_49,C_50,D_58),k1_relset_1(C_50,A_48,E_62))
      | ~ m1_subset_1(F_64,B_49)
      | ~ m1_subset_1(E_62,k1_zfmisc_1(k2_zfmisc_1(C_50,A_48)))
      | ~ v1_funct_1(E_62)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(B_49,C_50)))
      | ~ v1_funct_2(D_58,B_49,C_50)
      | ~ v1_funct_1(D_58)
      | v1_xboole_0(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_1616,plain,(
    ! [C_320,D_317,A_319,F_321,B_318,E_322] :
      ( k1_funct_1(k8_funct_2(B_318,C_320,A_319,D_317,E_322),F_321) = k1_funct_1(E_322,k1_funct_1(D_317,F_321))
      | k1_xboole_0 = B_318
      | ~ r1_tarski(k2_relset_1(B_318,C_320,D_317),k1_relset_1(C_320,A_319,E_322))
      | ~ m1_subset_1(F_321,B_318)
      | ~ m1_subset_1(E_322,k1_zfmisc_1(k2_zfmisc_1(C_320,A_319)))
      | ~ v1_funct_1(E_322)
      | ~ m1_subset_1(D_317,k1_zfmisc_1(k2_zfmisc_1(B_318,C_320)))
      | ~ v1_funct_2(D_317,B_318,C_320)
      | ~ v1_funct_1(D_317) ) ),
    inference(negUnitSimplification,[status(thm)],[c_582,c_60])).

tff(c_1632,plain,(
    ! [A_319,E_322,F_321] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5',A_319,'#skF_6',E_322),F_321) = k1_funct_1(E_322,k1_funct_1('#skF_6',F_321))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5',A_319,E_322))
      | ~ m1_subset_1(F_321,'#skF_4')
      | ~ m1_subset_1(E_322,k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_319)))
      | ~ v1_funct_1(E_322)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_1616])).

tff(c_1640,plain,(
    ! [A_319,E_322,F_321] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5',A_319,'#skF_6',E_322),F_321) = k1_funct_1(E_322,k1_funct_1('#skF_6',F_321))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5',A_319,E_322))
      | ~ m1_subset_1(F_321,'#skF_4')
      | ~ m1_subset_1(E_322,k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_319)))
      | ~ v1_funct_1(E_322) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_1632])).

tff(c_1812,plain,(
    ! [A_340,E_341,F_342] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5',A_340,'#skF_6',E_341),F_342) = k1_funct_1(E_341,k1_funct_1('#skF_6',F_342))
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5',A_340,E_341))
      | ~ m1_subset_1(F_342,'#skF_4')
      | ~ m1_subset_1(E_341,k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_340)))
      | ~ v1_funct_1(E_341) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1640])).

tff(c_1820,plain,(
    ! [F_342] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_342) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_342))
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_342,'#skF_4')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
      | ~ v1_funct_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_1812])).

tff(c_1822,plain,(
    ! [F_342] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_342) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_342))
      | ~ m1_subset_1(F_342,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_507,c_1820])).

tff(c_585,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | ~ m1_subset_1(A_13,B_14) ) ),
    inference(negUnitSimplification,[status(thm)],[c_582,c_20])).

tff(c_1125,plain,(
    ! [B_269,A_270,C_271] :
      ( k1_xboole_0 = B_269
      | k1_relset_1(A_270,B_269,C_271) = A_270
      | ~ v1_funct_2(C_271,A_270,B_269)
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_270,B_269))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1132,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_1125])).

tff(c_1139,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_459,c_1132])).

tff(c_1143,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1139])).

tff(c_658,plain,(
    ! [B_174,A_175] :
      ( r2_hidden(k1_funct_1(B_174,A_175),k2_relat_1(B_174))
      | ~ r2_hidden(A_175,k1_relat_1(B_174))
      | ~ v1_funct_1(B_174)
      | ~ v1_relat_1(B_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1975,plain,(
    ! [B_365,A_366,B_367] :
      ( r2_hidden(k1_funct_1(B_365,A_366),B_367)
      | ~ r1_tarski(k2_relat_1(B_365),B_367)
      | ~ r2_hidden(A_366,k1_relat_1(B_365))
      | ~ v1_funct_1(B_365)
      | ~ v1_relat_1(B_365) ) ),
    inference(resolution,[status(thm)],[c_658,c_6])).

tff(c_14065,plain,(
    ! [A_933,B_934,B_935,A_936] :
      ( k7_partfun1(A_933,B_934,k1_funct_1(B_935,A_936)) = k1_funct_1(B_934,k1_funct_1(B_935,A_936))
      | ~ v1_funct_1(B_934)
      | ~ v5_relat_1(B_934,A_933)
      | ~ v1_relat_1(B_934)
      | ~ r1_tarski(k2_relat_1(B_935),k1_relat_1(B_934))
      | ~ r2_hidden(A_936,k1_relat_1(B_935))
      | ~ v1_funct_1(B_935)
      | ~ v1_relat_1(B_935) ) ),
    inference(resolution,[status(thm)],[c_1975,c_54])).

tff(c_14081,plain,(
    ! [A_933,A_936] :
      ( k7_partfun1(A_933,'#skF_7',k1_funct_1('#skF_6',A_936)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_936))
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_933)
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(A_936,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_507,c_14065])).

tff(c_18120,plain,(
    ! [A_1075,A_1076] :
      ( k7_partfun1(A_1075,'#skF_7',k1_funct_1('#skF_6',A_1076)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_1076))
      | ~ v5_relat_1('#skF_7',A_1075)
      | ~ r2_hidden(A_1076,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_78,c_1143,c_208,c_72,c_14081])).

tff(c_18126,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ v5_relat_1('#skF_7','#skF_3')
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18120,c_62])).

tff(c_18132,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_18126])).

tff(c_18255,plain,(
    ~ r2_hidden('#skF_8','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_18132])).

tff(c_18261,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(resolution,[status(thm)],[c_585,c_18255])).

tff(c_18266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_18261])).

tff(c_18267,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_18132])).

tff(c_18951,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1822,c_18267])).

tff(c_18955,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_18951])).

tff(c_18956,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1139])).

tff(c_128,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_110])).

tff(c_19116,plain,(
    ! [A_1109] :
      ( A_1109 = '#skF_5'
      | ~ r1_tarski(A_1109,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18956,c_18956,c_128])).

tff(c_19270,plain,(
    ! [B_1133] :
      ( k1_relat_1(B_1133) = '#skF_5'
      | ~ v4_relat_1(B_1133,'#skF_5')
      | ~ v1_relat_1(B_1133) ) ),
    inference(resolution,[status(thm)],[c_28,c_19116])).

tff(c_19293,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_348,c_19270])).

tff(c_19311,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_19293])).

tff(c_19313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1002,c_19311])).

tff(c_19315,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1001])).

tff(c_19321,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19315,c_507])).

tff(c_19322,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19315,c_460])).

tff(c_28034,plain,(
    ! [D_1722,C_1725,B_1723,A_1724,E_1727,F_1726] :
      ( k1_funct_1(k8_funct_2(B_1723,C_1725,A_1724,D_1722,E_1727),F_1726) = k1_funct_1(E_1727,k1_funct_1(D_1722,F_1726))
      | k1_xboole_0 = B_1723
      | ~ r1_tarski(k2_relset_1(B_1723,C_1725,D_1722),k1_relset_1(C_1725,A_1724,E_1727))
      | ~ m1_subset_1(F_1726,B_1723)
      | ~ m1_subset_1(E_1727,k1_zfmisc_1(k2_zfmisc_1(C_1725,A_1724)))
      | ~ v1_funct_1(E_1727)
      | ~ m1_subset_1(D_1722,k1_zfmisc_1(k2_zfmisc_1(B_1723,C_1725)))
      | ~ v1_funct_2(D_1722,B_1723,C_1725)
      | ~ v1_funct_1(D_1722) ) ),
    inference(negUnitSimplification,[status(thm)],[c_582,c_60])).

tff(c_28050,plain,(
    ! [A_1724,E_1727,F_1726] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5',A_1724,'#skF_6',E_1727),F_1726) = k1_funct_1(E_1727,k1_funct_1('#skF_6',F_1726))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5',A_1724,E_1727))
      | ~ m1_subset_1(F_1726,'#skF_4')
      | ~ m1_subset_1(E_1727,k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_1724)))
      | ~ v1_funct_1(E_1727)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_28034])).

tff(c_28058,plain,(
    ! [A_1724,E_1727,F_1726] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5',A_1724,'#skF_6',E_1727),F_1726) = k1_funct_1(E_1727,k1_funct_1('#skF_6',F_1726))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5',A_1724,E_1727))
      | ~ m1_subset_1(F_1726,'#skF_4')
      | ~ m1_subset_1(E_1727,k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_1724)))
      | ~ v1_funct_1(E_1727) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_28050])).

tff(c_28399,plain,(
    ! [A_1762,E_1763,F_1764] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5',A_1762,'#skF_6',E_1763),F_1764) = k1_funct_1(E_1763,k1_funct_1('#skF_6',F_1764))
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5',A_1762,E_1763))
      | ~ m1_subset_1(F_1764,'#skF_4')
      | ~ m1_subset_1(E_1763,k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_1762)))
      | ~ v1_funct_1(E_1763) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_28058])).

tff(c_28401,plain,(
    ! [F_1764] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_1764) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_1764))
      | ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
      | ~ m1_subset_1(F_1764,'#skF_4')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
      | ~ v1_funct_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19322,c_28399])).

tff(c_31073,plain,(
    ! [F_1944] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_1944) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_1944))
      | ~ m1_subset_1(F_1944,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_19321,c_28401])).

tff(c_58,plain,(
    ! [A_44,B_45,C_46,D_47] :
      ( k3_funct_2(A_44,B_45,C_46,D_47) = k1_funct_1(C_46,D_47)
      | ~ m1_subset_1(D_47,A_44)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45)))
      | ~ v1_funct_2(C_46,A_44,B_45)
      | ~ v1_funct_1(C_46)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_27851,plain,(
    ! [A_1705,B_1706,C_1707,D_1708] :
      ( k3_funct_2(A_1705,B_1706,C_1707,D_1708) = k1_funct_1(C_1707,D_1708)
      | ~ m1_subset_1(D_1708,A_1705)
      | ~ m1_subset_1(C_1707,k1_zfmisc_1(k2_zfmisc_1(A_1705,B_1706)))
      | ~ v1_funct_2(C_1707,A_1705,B_1706)
      | ~ v1_funct_1(C_1707) ) ),
    inference(negUnitSimplification,[status(thm)],[c_582,c_58])).

tff(c_27970,plain,(
    ! [B_1718,C_1719] :
      ( k3_funct_2('#skF_4',B_1718,C_1719,'#skF_8') = k1_funct_1(C_1719,'#skF_8')
      | ~ m1_subset_1(C_1719,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_1718)))
      | ~ v1_funct_2(C_1719,'#skF_4',B_1718)
      | ~ v1_funct_1(C_1719) ) ),
    inference(resolution,[status(thm)],[c_68,c_27851])).

tff(c_27977,plain,
    ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_8') = k1_funct_1('#skF_6','#skF_8')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_27970])).

tff(c_27981,plain,(
    k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_8') = k1_funct_1('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_27977])).

tff(c_56,plain,(
    ! [A_40,B_41,C_42,D_43] :
      ( m1_subset_1(k3_funct_2(A_40,B_41,C_42,D_43),B_41)
      | ~ m1_subset_1(D_43,A_40)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | ~ v1_funct_2(C_42,A_40,B_41)
      | ~ v1_funct_1(C_42)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_27794,plain,(
    ! [A_1684,B_1685,C_1686,D_1687] :
      ( m1_subset_1(k3_funct_2(A_1684,B_1685,C_1686,D_1687),B_1685)
      | ~ m1_subset_1(D_1687,A_1684)
      | ~ m1_subset_1(C_1686,k1_zfmisc_1(k2_zfmisc_1(A_1684,B_1685)))
      | ~ v1_funct_2(C_1686,A_1684,B_1685)
      | ~ v1_funct_1(C_1686) ) ),
    inference(negUnitSimplification,[status(thm)],[c_582,c_56])).

tff(c_27799,plain,(
    ! [D_1687] :
      ( m1_subset_1(k3_funct_2('#skF_4','#skF_5','#skF_6',D_1687),'#skF_5')
      | ~ m1_subset_1(D_1687,'#skF_4')
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_74,c_27794])).

tff(c_27805,plain,(
    ! [D_1687] :
      ( m1_subset_1(k3_funct_2('#skF_4','#skF_5','#skF_6',D_1687),'#skF_5')
      | ~ m1_subset_1(D_1687,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_27799])).

tff(c_28023,plain,
    ( m1_subset_1(k1_funct_1('#skF_6','#skF_8'),'#skF_5')
    | ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_27981,c_27805])).

tff(c_28027,plain,(
    m1_subset_1(k1_funct_1('#skF_6','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_28023])).

tff(c_27658,plain,(
    ! [A_1676,B_1677,C_1678] :
      ( k7_partfun1(A_1676,B_1677,C_1678) = k1_funct_1(B_1677,C_1678)
      | ~ r2_hidden(C_1678,k1_relat_1(B_1677))
      | ~ v1_funct_1(B_1677)
      | ~ v5_relat_1(B_1677,A_1676)
      | ~ v1_relat_1(B_1677) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_28767,plain,(
    ! [A_1798,B_1799,A_1800] :
      ( k7_partfun1(A_1798,B_1799,A_1800) = k1_funct_1(B_1799,A_1800)
      | ~ v1_funct_1(B_1799)
      | ~ v5_relat_1(B_1799,A_1798)
      | ~ v1_relat_1(B_1799)
      | ~ m1_subset_1(A_1800,k1_relat_1(B_1799)) ) ),
    inference(resolution,[status(thm)],[c_585,c_27658])).

tff(c_28777,plain,(
    ! [A_1800] :
      ( k7_partfun1('#skF_3','#skF_7',A_1800) = k1_funct_1('#skF_7',A_1800)
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ m1_subset_1(A_1800,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_263,c_28767])).

tff(c_28802,plain,(
    ! [A_1801] :
      ( k7_partfun1('#skF_3','#skF_7',A_1801) = k1_funct_1('#skF_7',A_1801)
      | ~ m1_subset_1(A_1801,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19315,c_208,c_72,c_28777])).

tff(c_28809,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) = k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(resolution,[status(thm)],[c_28027,c_28802])).

tff(c_28836,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28809,c_62])).

tff(c_31079,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_31073,c_28836])).

tff(c_31093,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_31079])).

tff(c_31094,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_566])).

tff(c_102229,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102222,c_31094])).

tff(c_102244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_102229])).

tff(c_102246,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_31213])).

tff(c_132,plain,(
    ! [A_91] :
      ( k1_xboole_0 = A_91
      | ~ r1_tarski(A_91,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_110])).

tff(c_145,plain,(
    ! [A_85] :
      ( k1_xboole_0 = A_85
      | ~ v1_xboole_0(A_85) ) ),
    inference(resolution,[status(thm)],[c_108,c_132])).

tff(c_102257,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_102246,c_145])).

tff(c_102264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_102257])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:27:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.30/17.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.30/17.62  
% 27.30/17.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.44/17.62  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 27.44/17.62  
% 27.44/17.62  %Foreground sorts:
% 27.44/17.62  
% 27.44/17.62  
% 27.44/17.62  %Background operators:
% 27.44/17.62  
% 27.44/17.62  
% 27.44/17.62  %Foreground operators:
% 27.44/17.62  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 27.44/17.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 27.44/17.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.44/17.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 27.44/17.62  tff('#skF_1', type, '#skF_1': $i > $i).
% 27.44/17.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 27.44/17.62  tff('#skF_7', type, '#skF_7': $i).
% 27.44/17.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.44/17.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 27.44/17.62  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 27.44/17.62  tff('#skF_5', type, '#skF_5': $i).
% 27.44/17.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 27.44/17.62  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 27.44/17.62  tff('#skF_6', type, '#skF_6': $i).
% 27.44/17.62  tff('#skF_3', type, '#skF_3': $i).
% 27.44/17.62  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 27.44/17.62  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 27.44/17.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 27.44/17.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 27.44/17.62  tff('#skF_8', type, '#skF_8': $i).
% 27.44/17.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.44/17.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 27.44/17.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 27.44/17.62  tff('#skF_4', type, '#skF_4': $i).
% 27.44/17.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.44/17.62  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 27.44/17.62  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 27.44/17.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 27.44/17.62  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 27.44/17.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 27.44/17.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 27.44/17.62  
% 27.44/17.65  tff(f_192, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 27.44/17.65  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 27.44/17.65  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 27.44/17.65  tff(f_167, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 27.44/17.65  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 27.44/17.65  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 27.44/17.65  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 27.44/17.65  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 27.44/17.65  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 27.44/17.65  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 27.44/17.65  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 27.44/17.65  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 27.44/17.65  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 27.44/17.65  tff(f_117, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 27.44/17.65  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 27.44/17.65  tff(f_143, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 27.44/17.65  tff(f_130, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => m1_subset_1(k3_funct_2(A, B, C, D), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_funct_2)).
% 27.44/17.65  tff(c_64, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_192])).
% 27.44/17.65  tff(c_80, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_192])).
% 27.44/17.65  tff(c_68, plain, (m1_subset_1('#skF_8', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_192])).
% 27.44/17.65  tff(c_78, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_192])).
% 27.44/17.65  tff(c_76, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_192])).
% 27.44/17.65  tff(c_74, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 27.44/17.65  tff(c_70, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_192])).
% 27.44/17.65  tff(c_447, plain, (![A_144, B_145, C_146]: (k1_relset_1(A_144, B_145, C_146)=k1_relat_1(C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 27.44/17.65  tff(c_460, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_70, c_447])).
% 27.44/17.65  tff(c_349, plain, (![A_135, B_136, C_137]: (k2_relset_1(A_135, B_136, C_137)=k2_relat_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 27.44/17.65  tff(c_361, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_349])).
% 27.44/17.65  tff(c_66, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_192])).
% 27.44/17.65  tff(c_363, plain, (r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_361, c_66])).
% 27.44/17.65  tff(c_507, plain, (r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_460, c_363])).
% 27.44/17.65  tff(c_72, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_192])).
% 27.44/17.65  tff(c_32233, plain, (![F_2057, D_2053, A_2055, B_2054, E_2058, C_2056]: (k1_funct_1(k8_funct_2(B_2054, C_2056, A_2055, D_2053, E_2058), F_2057)=k1_funct_1(E_2058, k1_funct_1(D_2053, F_2057)) | k1_xboole_0=B_2054 | ~r1_tarski(k2_relset_1(B_2054, C_2056, D_2053), k1_relset_1(C_2056, A_2055, E_2058)) | ~m1_subset_1(F_2057, B_2054) | ~m1_subset_1(E_2058, k1_zfmisc_1(k2_zfmisc_1(C_2056, A_2055))) | ~v1_funct_1(E_2058) | ~m1_subset_1(D_2053, k1_zfmisc_1(k2_zfmisc_1(B_2054, C_2056))) | ~v1_funct_2(D_2053, B_2054, C_2056) | ~v1_funct_1(D_2053) | v1_xboole_0(C_2056))), inference(cnfTransformation, [status(thm)], [f_167])).
% 27.44/17.65  tff(c_32245, plain, (![B_2054, D_2053, F_2057]: (k1_funct_1(k8_funct_2(B_2054, '#skF_5', '#skF_3', D_2053, '#skF_7'), F_2057)=k1_funct_1('#skF_7', k1_funct_1(D_2053, F_2057)) | k1_xboole_0=B_2054 | ~r1_tarski(k2_relset_1(B_2054, '#skF_5', D_2053), k1_relat_1('#skF_7')) | ~m1_subset_1(F_2057, B_2054) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1(D_2053, k1_zfmisc_1(k2_zfmisc_1(B_2054, '#skF_5'))) | ~v1_funct_2(D_2053, B_2054, '#skF_5') | ~v1_funct_1(D_2053) | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_460, c_32233])).
% 27.44/17.65  tff(c_32257, plain, (![B_2054, D_2053, F_2057]: (k1_funct_1(k8_funct_2(B_2054, '#skF_5', '#skF_3', D_2053, '#skF_7'), F_2057)=k1_funct_1('#skF_7', k1_funct_1(D_2053, F_2057)) | k1_xboole_0=B_2054 | ~r1_tarski(k2_relset_1(B_2054, '#skF_5', D_2053), k1_relat_1('#skF_7')) | ~m1_subset_1(F_2057, B_2054) | ~m1_subset_1(D_2053, k1_zfmisc_1(k2_zfmisc_1(B_2054, '#skF_5'))) | ~v1_funct_2(D_2053, B_2054, '#skF_5') | ~v1_funct_1(D_2053) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_32245])).
% 27.44/17.65  tff(c_77144, plain, (![B_3197, D_3198, F_3199]: (k1_funct_1(k8_funct_2(B_3197, '#skF_5', '#skF_3', D_3198, '#skF_7'), F_3199)=k1_funct_1('#skF_7', k1_funct_1(D_3198, F_3199)) | k1_xboole_0=B_3197 | ~r1_tarski(k2_relset_1(B_3197, '#skF_5', D_3198), k1_relat_1('#skF_7')) | ~m1_subset_1(F_3199, B_3197) | ~m1_subset_1(D_3198, k1_zfmisc_1(k2_zfmisc_1(B_3197, '#skF_5'))) | ~v1_funct_2(D_3198, B_3197, '#skF_5') | ~v1_funct_1(D_3198))), inference(negUnitSimplification, [status(thm)], [c_80, c_32257])).
% 27.44/17.65  tff(c_77152, plain, (![F_3199]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_3199)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_3199)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7')) | ~m1_subset_1(F_3199, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_361, c_77144])).
% 27.44/17.65  tff(c_77157, plain, (![F_3199]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_3199)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_3199)) | k1_xboole_0='#skF_4' | ~m1_subset_1(F_3199, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_507, c_77152])).
% 27.44/17.65  tff(c_77158, plain, (![F_3199]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_3199)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_3199)) | ~m1_subset_1(F_3199, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_64, c_77157])).
% 27.44/17.65  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 27.44/17.65  tff(c_195, plain, (![C_101, A_102, B_103]: (v1_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 27.44/17.65  tff(c_207, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_195])).
% 27.44/17.65  tff(c_459, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_447])).
% 27.44/17.65  tff(c_31524, plain, (![B_1983, A_1984, C_1985]: (k1_xboole_0=B_1983 | k1_relset_1(A_1984, B_1983, C_1985)=A_1984 | ~v1_funct_2(C_1985, A_1984, B_1983) | ~m1_subset_1(C_1985, k1_zfmisc_1(k2_zfmisc_1(A_1984, B_1983))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 27.44/17.65  tff(c_31531, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_74, c_31524])).
% 27.44/17.65  tff(c_31538, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_459, c_31531])).
% 27.44/17.65  tff(c_31541, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_31538])).
% 27.44/17.65  tff(c_26, plain, (![B_18, A_17]: (v4_relat_1(B_18, A_17) | ~r1_tarski(k1_relat_1(B_18), A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 27.44/17.65  tff(c_31557, plain, (![A_17]: (v4_relat_1('#skF_6', A_17) | ~r1_tarski('#skF_4', A_17) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_31541, c_26])).
% 27.44/17.65  tff(c_31573, plain, (![A_17]: (v4_relat_1('#skF_6', A_17) | ~r1_tarski('#skF_4', A_17))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_31557])).
% 27.44/17.65  tff(c_335, plain, (![C_132, A_133, B_134]: (v4_relat_1(C_132, A_133) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 27.44/17.65  tff(c_347, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_335])).
% 27.44/17.65  tff(c_290, plain, (![B_119, A_120]: (r1_tarski(k1_relat_1(B_119), A_120) | ~v4_relat_1(B_119, A_120) | ~v1_relat_1(B_119))), inference(cnfTransformation, [status(thm)], [f_62])).
% 27.44/17.65  tff(c_104, plain, (![A_85, B_86]: (r2_hidden('#skF_2'(A_85, B_86), A_85) | r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_38])).
% 27.44/17.65  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 27.44/17.65  tff(c_108, plain, (![A_85, B_86]: (~v1_xboole_0(A_85) | r1_tarski(A_85, B_86))), inference(resolution, [status(thm)], [c_104, c_2])).
% 27.44/17.65  tff(c_110, plain, (![B_89, A_90]: (B_89=A_90 | ~r1_tarski(B_89, A_90) | ~r1_tarski(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_44])).
% 27.44/17.65  tff(c_121, plain, (![B_86, A_85]: (B_86=A_85 | ~r1_tarski(B_86, A_85) | ~v1_xboole_0(A_85))), inference(resolution, [status(thm)], [c_108, c_110])).
% 27.44/17.65  tff(c_31176, plain, (![B_1956, A_1957]: (k1_relat_1(B_1956)=A_1957 | ~v1_xboole_0(A_1957) | ~v4_relat_1(B_1956, A_1957) | ~v1_relat_1(B_1956))), inference(resolution, [status(thm)], [c_290, c_121])).
% 27.44/17.65  tff(c_31194, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_xboole_0('#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_347, c_31176])).
% 27.44/17.65  tff(c_31213, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_31194])).
% 27.44/17.65  tff(c_31216, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_31213])).
% 27.44/17.65  tff(c_28, plain, (![B_18, A_17]: (r1_tarski(k1_relat_1(B_18), A_17) | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 27.44/17.65  tff(c_20, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | v1_xboole_0(B_14) | ~m1_subset_1(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 27.44/17.65  tff(c_238, plain, (![C_110, B_111, A_112]: (r2_hidden(C_110, B_111) | ~r2_hidden(C_110, A_112) | ~r1_tarski(A_112, B_111))), inference(cnfTransformation, [status(thm)], [f_38])).
% 27.44/17.65  tff(c_31703, plain, (![A_1995, B_1996, B_1997]: (r2_hidden(A_1995, B_1996) | ~r1_tarski(B_1997, B_1996) | v1_xboole_0(B_1997) | ~m1_subset_1(A_1995, B_1997))), inference(resolution, [status(thm)], [c_20, c_238])).
% 27.44/17.65  tff(c_85301, plain, (![A_3490, A_3491, B_3492]: (r2_hidden(A_3490, A_3491) | v1_xboole_0(k1_relat_1(B_3492)) | ~m1_subset_1(A_3490, k1_relat_1(B_3492)) | ~v4_relat_1(B_3492, A_3491) | ~v1_relat_1(B_3492))), inference(resolution, [status(thm)], [c_28, c_31703])).
% 27.44/17.65  tff(c_85309, plain, (![A_3490, A_3491]: (r2_hidden(A_3490, A_3491) | v1_xboole_0(k1_relat_1('#skF_6')) | ~m1_subset_1(A_3490, '#skF_4') | ~v4_relat_1('#skF_6', A_3491) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_31541, c_85301])).
% 27.44/17.65  tff(c_85319, plain, (![A_3490, A_3491]: (r2_hidden(A_3490, A_3491) | v1_xboole_0('#skF_4') | ~m1_subset_1(A_3490, '#skF_4') | ~v4_relat_1('#skF_6', A_3491))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_31541, c_85309])).
% 27.44/17.65  tff(c_89094, plain, (![A_3602, A_3603]: (r2_hidden(A_3602, A_3603) | ~m1_subset_1(A_3602, '#skF_4') | ~v4_relat_1('#skF_6', A_3603))), inference(negUnitSimplification, [status(thm)], [c_31216, c_85319])).
% 27.44/17.65  tff(c_89131, plain, (![A_3602, A_17]: (r2_hidden(A_3602, A_17) | ~m1_subset_1(A_3602, '#skF_4') | ~r1_tarski('#skF_4', A_17))), inference(resolution, [status(thm)], [c_31573, c_89094])).
% 27.44/17.65  tff(c_250, plain, (![C_113, B_114, A_115]: (v5_relat_1(C_113, B_114) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_115, B_114))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 27.44/17.65  tff(c_263, plain, (v5_relat_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_250])).
% 27.44/17.65  tff(c_208, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_70, c_195])).
% 27.44/17.65  tff(c_31217, plain, (![B_1958, A_1959]: (r2_hidden(k1_funct_1(B_1958, A_1959), k2_relat_1(B_1958)) | ~r2_hidden(A_1959, k1_relat_1(B_1958)) | ~v1_funct_1(B_1958) | ~v1_relat_1(B_1958))), inference(cnfTransformation, [status(thm)], [f_70])).
% 27.44/17.65  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 27.44/17.65  tff(c_77643, plain, (![B_3233, A_3234, B_3235]: (r2_hidden(k1_funct_1(B_3233, A_3234), B_3235) | ~r1_tarski(k2_relat_1(B_3233), B_3235) | ~r2_hidden(A_3234, k1_relat_1(B_3233)) | ~v1_funct_1(B_3233) | ~v1_relat_1(B_3233))), inference(resolution, [status(thm)], [c_31217, c_6])).
% 27.44/17.65  tff(c_54, plain, (![A_36, B_37, C_39]: (k7_partfun1(A_36, B_37, C_39)=k1_funct_1(B_37, C_39) | ~r2_hidden(C_39, k1_relat_1(B_37)) | ~v1_funct_1(B_37) | ~v5_relat_1(B_37, A_36) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_117])).
% 27.44/17.65  tff(c_90572, plain, (![A_3634, B_3635, B_3636, A_3637]: (k7_partfun1(A_3634, B_3635, k1_funct_1(B_3636, A_3637))=k1_funct_1(B_3635, k1_funct_1(B_3636, A_3637)) | ~v1_funct_1(B_3635) | ~v5_relat_1(B_3635, A_3634) | ~v1_relat_1(B_3635) | ~r1_tarski(k2_relat_1(B_3636), k1_relat_1(B_3635)) | ~r2_hidden(A_3637, k1_relat_1(B_3636)) | ~v1_funct_1(B_3636) | ~v1_relat_1(B_3636))), inference(resolution, [status(thm)], [c_77643, c_54])).
% 27.44/17.65  tff(c_90598, plain, (![A_3634, A_3637]: (k7_partfun1(A_3634, '#skF_7', k1_funct_1('#skF_6', A_3637))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_3637)) | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_3634) | ~v1_relat_1('#skF_7') | ~r2_hidden(A_3637, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_507, c_90572])).
% 27.44/17.65  tff(c_101653, plain, (![A_3874, A_3875]: (k7_partfun1(A_3874, '#skF_7', k1_funct_1('#skF_6', A_3875))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_3875)) | ~v5_relat_1('#skF_7', A_3874) | ~r2_hidden(A_3875, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_78, c_31541, c_208, c_72, c_90598])).
% 27.44/17.65  tff(c_62, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))!=k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_192])).
% 27.44/17.65  tff(c_101659, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~v5_relat_1('#skF_7', '#skF_3') | ~r2_hidden('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_101653, c_62])).
% 27.44/17.65  tff(c_101665, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~r2_hidden('#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_263, c_101659])).
% 27.44/17.65  tff(c_101774, plain, (~r2_hidden('#skF_8', '#skF_4')), inference(splitLeft, [status(thm)], [c_101665])).
% 27.44/17.65  tff(c_101777, plain, (~m1_subset_1('#skF_8', '#skF_4') | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_89131, c_101774])).
% 27.44/17.65  tff(c_101787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_68, c_101777])).
% 27.44/17.65  tff(c_101788, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_101665])).
% 27.44/17.65  tff(c_102217, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_77158, c_101788])).
% 27.44/17.65  tff(c_102221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_102217])).
% 27.44/17.65  tff(c_102222, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_31538])).
% 27.44/17.65  tff(c_986, plain, (![B_246, C_247, A_248]: (k1_xboole_0=B_246 | v1_funct_2(C_247, A_248, B_246) | k1_relset_1(A_248, B_246, C_247)!=A_248 | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_248, B_246))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 27.44/17.65  tff(c_996, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_7', '#skF_5', '#skF_3') | k1_relset_1('#skF_5', '#skF_3', '#skF_7')!='#skF_5'), inference(resolution, [status(thm)], [c_70, c_986])).
% 27.44/17.65  tff(c_1001, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_7', '#skF_5', '#skF_3') | k1_relat_1('#skF_7')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_460, c_996])).
% 27.44/17.65  tff(c_1002, plain, (k1_relat_1('#skF_7')!='#skF_5'), inference(splitLeft, [status(thm)], [c_1001])).
% 27.44/17.65  tff(c_348, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_70, c_335])).
% 27.44/17.65  tff(c_18, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 27.44/17.65  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 27.44/17.65  tff(c_530, plain, (![A_155, B_156]: (r2_hidden('#skF_1'(A_155), B_156) | ~r1_tarski(A_155, B_156) | v1_xboole_0(A_155))), inference(resolution, [status(thm)], [c_4, c_238])).
% 27.44/17.65  tff(c_538, plain, (![B_157, A_158]: (~v1_xboole_0(B_157) | ~r1_tarski(A_158, B_157) | v1_xboole_0(A_158))), inference(resolution, [status(thm)], [c_530, c_2])).
% 27.44/17.65  tff(c_566, plain, (![A_12]: (~v1_xboole_0(A_12) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_538])).
% 27.44/17.65  tff(c_582, plain, (![A_12]: (~v1_xboole_0(A_12))), inference(splitLeft, [status(thm)], [c_566])).
% 27.44/17.65  tff(c_60, plain, (![B_49, F_64, E_62, A_48, C_50, D_58]: (k1_funct_1(k8_funct_2(B_49, C_50, A_48, D_58, E_62), F_64)=k1_funct_1(E_62, k1_funct_1(D_58, F_64)) | k1_xboole_0=B_49 | ~r1_tarski(k2_relset_1(B_49, C_50, D_58), k1_relset_1(C_50, A_48, E_62)) | ~m1_subset_1(F_64, B_49) | ~m1_subset_1(E_62, k1_zfmisc_1(k2_zfmisc_1(C_50, A_48))) | ~v1_funct_1(E_62) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(B_49, C_50))) | ~v1_funct_2(D_58, B_49, C_50) | ~v1_funct_1(D_58) | v1_xboole_0(C_50))), inference(cnfTransformation, [status(thm)], [f_167])).
% 27.44/17.65  tff(c_1616, plain, (![C_320, D_317, A_319, F_321, B_318, E_322]: (k1_funct_1(k8_funct_2(B_318, C_320, A_319, D_317, E_322), F_321)=k1_funct_1(E_322, k1_funct_1(D_317, F_321)) | k1_xboole_0=B_318 | ~r1_tarski(k2_relset_1(B_318, C_320, D_317), k1_relset_1(C_320, A_319, E_322)) | ~m1_subset_1(F_321, B_318) | ~m1_subset_1(E_322, k1_zfmisc_1(k2_zfmisc_1(C_320, A_319))) | ~v1_funct_1(E_322) | ~m1_subset_1(D_317, k1_zfmisc_1(k2_zfmisc_1(B_318, C_320))) | ~v1_funct_2(D_317, B_318, C_320) | ~v1_funct_1(D_317))), inference(negUnitSimplification, [status(thm)], [c_582, c_60])).
% 27.44/17.65  tff(c_1632, plain, (![A_319, E_322, F_321]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', A_319, '#skF_6', E_322), F_321)=k1_funct_1(E_322, k1_funct_1('#skF_6', F_321)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', A_319, E_322)) | ~m1_subset_1(F_321, '#skF_4') | ~m1_subset_1(E_322, k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_319))) | ~v1_funct_1(E_322) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_361, c_1616])).
% 27.44/17.65  tff(c_1640, plain, (![A_319, E_322, F_321]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', A_319, '#skF_6', E_322), F_321)=k1_funct_1(E_322, k1_funct_1('#skF_6', F_321)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', A_319, E_322)) | ~m1_subset_1(F_321, '#skF_4') | ~m1_subset_1(E_322, k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_319))) | ~v1_funct_1(E_322))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_1632])).
% 27.44/17.65  tff(c_1812, plain, (![A_340, E_341, F_342]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', A_340, '#skF_6', E_341), F_342)=k1_funct_1(E_341, k1_funct_1('#skF_6', F_342)) | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', A_340, E_341)) | ~m1_subset_1(F_342, '#skF_4') | ~m1_subset_1(E_341, k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_340))) | ~v1_funct_1(E_341))), inference(negUnitSimplification, [status(thm)], [c_64, c_1640])).
% 27.44/17.65  tff(c_1820, plain, (![F_342]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_342)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_342)) | ~r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7')) | ~m1_subset_1(F_342, '#skF_4') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_460, c_1812])).
% 27.44/17.65  tff(c_1822, plain, (![F_342]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_342)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_342)) | ~m1_subset_1(F_342, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_507, c_1820])).
% 27.44/17.65  tff(c_585, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | ~m1_subset_1(A_13, B_14))), inference(negUnitSimplification, [status(thm)], [c_582, c_20])).
% 27.44/17.65  tff(c_1125, plain, (![B_269, A_270, C_271]: (k1_xboole_0=B_269 | k1_relset_1(A_270, B_269, C_271)=A_270 | ~v1_funct_2(C_271, A_270, B_269) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_270, B_269))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 27.44/17.65  tff(c_1132, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_74, c_1125])).
% 27.44/17.65  tff(c_1139, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_459, c_1132])).
% 27.44/17.65  tff(c_1143, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_1139])).
% 27.44/17.65  tff(c_658, plain, (![B_174, A_175]: (r2_hidden(k1_funct_1(B_174, A_175), k2_relat_1(B_174)) | ~r2_hidden(A_175, k1_relat_1(B_174)) | ~v1_funct_1(B_174) | ~v1_relat_1(B_174))), inference(cnfTransformation, [status(thm)], [f_70])).
% 27.44/17.65  tff(c_1975, plain, (![B_365, A_366, B_367]: (r2_hidden(k1_funct_1(B_365, A_366), B_367) | ~r1_tarski(k2_relat_1(B_365), B_367) | ~r2_hidden(A_366, k1_relat_1(B_365)) | ~v1_funct_1(B_365) | ~v1_relat_1(B_365))), inference(resolution, [status(thm)], [c_658, c_6])).
% 27.44/17.65  tff(c_14065, plain, (![A_933, B_934, B_935, A_936]: (k7_partfun1(A_933, B_934, k1_funct_1(B_935, A_936))=k1_funct_1(B_934, k1_funct_1(B_935, A_936)) | ~v1_funct_1(B_934) | ~v5_relat_1(B_934, A_933) | ~v1_relat_1(B_934) | ~r1_tarski(k2_relat_1(B_935), k1_relat_1(B_934)) | ~r2_hidden(A_936, k1_relat_1(B_935)) | ~v1_funct_1(B_935) | ~v1_relat_1(B_935))), inference(resolution, [status(thm)], [c_1975, c_54])).
% 27.44/17.65  tff(c_14081, plain, (![A_933, A_936]: (k7_partfun1(A_933, '#skF_7', k1_funct_1('#skF_6', A_936))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_936)) | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_933) | ~v1_relat_1('#skF_7') | ~r2_hidden(A_936, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_507, c_14065])).
% 27.44/17.65  tff(c_18120, plain, (![A_1075, A_1076]: (k7_partfun1(A_1075, '#skF_7', k1_funct_1('#skF_6', A_1076))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_1076)) | ~v5_relat_1('#skF_7', A_1075) | ~r2_hidden(A_1076, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_78, c_1143, c_208, c_72, c_14081])).
% 27.44/17.65  tff(c_18126, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~v5_relat_1('#skF_7', '#skF_3') | ~r2_hidden('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18120, c_62])).
% 27.44/17.65  tff(c_18132, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~r2_hidden('#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_263, c_18126])).
% 27.44/17.65  tff(c_18255, plain, (~r2_hidden('#skF_8', '#skF_4')), inference(splitLeft, [status(thm)], [c_18132])).
% 27.44/17.65  tff(c_18261, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(resolution, [status(thm)], [c_585, c_18255])).
% 27.44/17.65  tff(c_18266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_18261])).
% 27.44/17.65  tff(c_18267, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_18132])).
% 27.44/17.65  tff(c_18951, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1822, c_18267])).
% 27.44/17.65  tff(c_18955, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_18951])).
% 27.44/17.65  tff(c_18956, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1139])).
% 27.44/17.65  tff(c_128, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_110])).
% 27.44/17.65  tff(c_19116, plain, (![A_1109]: (A_1109='#skF_5' | ~r1_tarski(A_1109, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_18956, c_18956, c_128])).
% 27.44/17.65  tff(c_19270, plain, (![B_1133]: (k1_relat_1(B_1133)='#skF_5' | ~v4_relat_1(B_1133, '#skF_5') | ~v1_relat_1(B_1133))), inference(resolution, [status(thm)], [c_28, c_19116])).
% 27.44/17.65  tff(c_19293, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_348, c_19270])).
% 27.44/17.65  tff(c_19311, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_208, c_19293])).
% 27.44/17.65  tff(c_19313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1002, c_19311])).
% 27.44/17.65  tff(c_19315, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_1001])).
% 27.44/17.65  tff(c_19321, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_19315, c_507])).
% 27.44/17.65  tff(c_19322, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_19315, c_460])).
% 27.44/17.65  tff(c_28034, plain, (![D_1722, C_1725, B_1723, A_1724, E_1727, F_1726]: (k1_funct_1(k8_funct_2(B_1723, C_1725, A_1724, D_1722, E_1727), F_1726)=k1_funct_1(E_1727, k1_funct_1(D_1722, F_1726)) | k1_xboole_0=B_1723 | ~r1_tarski(k2_relset_1(B_1723, C_1725, D_1722), k1_relset_1(C_1725, A_1724, E_1727)) | ~m1_subset_1(F_1726, B_1723) | ~m1_subset_1(E_1727, k1_zfmisc_1(k2_zfmisc_1(C_1725, A_1724))) | ~v1_funct_1(E_1727) | ~m1_subset_1(D_1722, k1_zfmisc_1(k2_zfmisc_1(B_1723, C_1725))) | ~v1_funct_2(D_1722, B_1723, C_1725) | ~v1_funct_1(D_1722))), inference(negUnitSimplification, [status(thm)], [c_582, c_60])).
% 27.44/17.65  tff(c_28050, plain, (![A_1724, E_1727, F_1726]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', A_1724, '#skF_6', E_1727), F_1726)=k1_funct_1(E_1727, k1_funct_1('#skF_6', F_1726)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', A_1724, E_1727)) | ~m1_subset_1(F_1726, '#skF_4') | ~m1_subset_1(E_1727, k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_1724))) | ~v1_funct_1(E_1727) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_361, c_28034])).
% 27.44/17.65  tff(c_28058, plain, (![A_1724, E_1727, F_1726]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', A_1724, '#skF_6', E_1727), F_1726)=k1_funct_1(E_1727, k1_funct_1('#skF_6', F_1726)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', A_1724, E_1727)) | ~m1_subset_1(F_1726, '#skF_4') | ~m1_subset_1(E_1727, k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_1724))) | ~v1_funct_1(E_1727))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_28050])).
% 27.44/17.65  tff(c_28399, plain, (![A_1762, E_1763, F_1764]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', A_1762, '#skF_6', E_1763), F_1764)=k1_funct_1(E_1763, k1_funct_1('#skF_6', F_1764)) | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', A_1762, E_1763)) | ~m1_subset_1(F_1764, '#skF_4') | ~m1_subset_1(E_1763, k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_1762))) | ~v1_funct_1(E_1763))), inference(negUnitSimplification, [status(thm)], [c_64, c_28058])).
% 27.44/17.65  tff(c_28401, plain, (![F_1764]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_1764)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_1764)) | ~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | ~m1_subset_1(F_1764, '#skF_4') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_19322, c_28399])).
% 27.44/17.65  tff(c_31073, plain, (![F_1944]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_1944)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_1944)) | ~m1_subset_1(F_1944, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_19321, c_28401])).
% 27.44/17.65  tff(c_58, plain, (![A_44, B_45, C_46, D_47]: (k3_funct_2(A_44, B_45, C_46, D_47)=k1_funct_1(C_46, D_47) | ~m1_subset_1(D_47, A_44) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))) | ~v1_funct_2(C_46, A_44, B_45) | ~v1_funct_1(C_46) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_143])).
% 27.44/17.65  tff(c_27851, plain, (![A_1705, B_1706, C_1707, D_1708]: (k3_funct_2(A_1705, B_1706, C_1707, D_1708)=k1_funct_1(C_1707, D_1708) | ~m1_subset_1(D_1708, A_1705) | ~m1_subset_1(C_1707, k1_zfmisc_1(k2_zfmisc_1(A_1705, B_1706))) | ~v1_funct_2(C_1707, A_1705, B_1706) | ~v1_funct_1(C_1707))), inference(negUnitSimplification, [status(thm)], [c_582, c_58])).
% 27.44/17.65  tff(c_27970, plain, (![B_1718, C_1719]: (k3_funct_2('#skF_4', B_1718, C_1719, '#skF_8')=k1_funct_1(C_1719, '#skF_8') | ~m1_subset_1(C_1719, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_1718))) | ~v1_funct_2(C_1719, '#skF_4', B_1718) | ~v1_funct_1(C_1719))), inference(resolution, [status(thm)], [c_68, c_27851])).
% 27.44/17.65  tff(c_27977, plain, (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_8')=k1_funct_1('#skF_6', '#skF_8') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_74, c_27970])).
% 27.44/17.65  tff(c_27981, plain, (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_8')=k1_funct_1('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_27977])).
% 27.44/17.65  tff(c_56, plain, (![A_40, B_41, C_42, D_43]: (m1_subset_1(k3_funct_2(A_40, B_41, C_42, D_43), B_41) | ~m1_subset_1(D_43, A_40) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))) | ~v1_funct_2(C_42, A_40, B_41) | ~v1_funct_1(C_42) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_130])).
% 27.44/17.65  tff(c_27794, plain, (![A_1684, B_1685, C_1686, D_1687]: (m1_subset_1(k3_funct_2(A_1684, B_1685, C_1686, D_1687), B_1685) | ~m1_subset_1(D_1687, A_1684) | ~m1_subset_1(C_1686, k1_zfmisc_1(k2_zfmisc_1(A_1684, B_1685))) | ~v1_funct_2(C_1686, A_1684, B_1685) | ~v1_funct_1(C_1686))), inference(negUnitSimplification, [status(thm)], [c_582, c_56])).
% 27.44/17.65  tff(c_27799, plain, (![D_1687]: (m1_subset_1(k3_funct_2('#skF_4', '#skF_5', '#skF_6', D_1687), '#skF_5') | ~m1_subset_1(D_1687, '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_74, c_27794])).
% 27.44/17.65  tff(c_27805, plain, (![D_1687]: (m1_subset_1(k3_funct_2('#skF_4', '#skF_5', '#skF_6', D_1687), '#skF_5') | ~m1_subset_1(D_1687, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_27799])).
% 27.44/17.65  tff(c_28023, plain, (m1_subset_1(k1_funct_1('#skF_6', '#skF_8'), '#skF_5') | ~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_27981, c_27805])).
% 27.44/17.65  tff(c_28027, plain, (m1_subset_1(k1_funct_1('#skF_6', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_28023])).
% 27.44/17.65  tff(c_27658, plain, (![A_1676, B_1677, C_1678]: (k7_partfun1(A_1676, B_1677, C_1678)=k1_funct_1(B_1677, C_1678) | ~r2_hidden(C_1678, k1_relat_1(B_1677)) | ~v1_funct_1(B_1677) | ~v5_relat_1(B_1677, A_1676) | ~v1_relat_1(B_1677))), inference(cnfTransformation, [status(thm)], [f_117])).
% 27.44/17.65  tff(c_28767, plain, (![A_1798, B_1799, A_1800]: (k7_partfun1(A_1798, B_1799, A_1800)=k1_funct_1(B_1799, A_1800) | ~v1_funct_1(B_1799) | ~v5_relat_1(B_1799, A_1798) | ~v1_relat_1(B_1799) | ~m1_subset_1(A_1800, k1_relat_1(B_1799)))), inference(resolution, [status(thm)], [c_585, c_27658])).
% 27.44/17.65  tff(c_28777, plain, (![A_1800]: (k7_partfun1('#skF_3', '#skF_7', A_1800)=k1_funct_1('#skF_7', A_1800) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~m1_subset_1(A_1800, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_263, c_28767])).
% 27.44/17.65  tff(c_28802, plain, (![A_1801]: (k7_partfun1('#skF_3', '#skF_7', A_1801)=k1_funct_1('#skF_7', A_1801) | ~m1_subset_1(A_1801, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_19315, c_208, c_72, c_28777])).
% 27.44/17.65  tff(c_28809, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(resolution, [status(thm)], [c_28027, c_28802])).
% 27.44/17.65  tff(c_28836, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_28809, c_62])).
% 27.44/17.65  tff(c_31079, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_31073, c_28836])).
% 27.44/17.65  tff(c_31093, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_31079])).
% 27.44/17.65  tff(c_31094, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_566])).
% 27.44/17.65  tff(c_102229, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_102222, c_31094])).
% 27.44/17.65  tff(c_102244, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_102229])).
% 27.44/17.65  tff(c_102246, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_31213])).
% 27.44/17.65  tff(c_132, plain, (![A_91]: (k1_xboole_0=A_91 | ~r1_tarski(A_91, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_110])).
% 27.44/17.65  tff(c_145, plain, (![A_85]: (k1_xboole_0=A_85 | ~v1_xboole_0(A_85))), inference(resolution, [status(thm)], [c_108, c_132])).
% 27.44/17.65  tff(c_102257, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_102246, c_145])).
% 27.44/17.65  tff(c_102264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_102257])).
% 27.44/17.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.44/17.65  
% 27.44/17.65  Inference rules
% 27.44/17.65  ----------------------
% 27.44/17.65  #Ref     : 0
% 27.44/17.65  #Sup     : 22037
% 27.44/17.65  #Fact    : 0
% 27.44/17.65  #Define  : 0
% 27.44/17.65  #Split   : 231
% 27.44/17.65  #Chain   : 0
% 27.44/17.65  #Close   : 0
% 27.44/17.65  
% 27.44/17.65  Ordering : KBO
% 27.44/17.65  
% 27.44/17.65  Simplification rules
% 27.44/17.65  ----------------------
% 27.44/17.66  #Subsume      : 9028
% 27.44/17.66  #Demod        : 24197
% 27.44/17.66  #Tautology    : 5507
% 27.44/17.66  #SimpNegUnit  : 580
% 27.44/17.66  #BackRed      : 776
% 27.44/17.66  
% 27.44/17.66  #Partial instantiations: 0
% 27.44/17.66  #Strategies tried      : 1
% 27.44/17.66  
% 27.44/17.66  Timing (in seconds)
% 27.44/17.66  ----------------------
% 27.44/17.66  Preprocessing        : 0.38
% 27.44/17.66  Parsing              : 0.19
% 27.44/17.66  CNF conversion       : 0.03
% 27.44/17.66  Main loop            : 16.49
% 27.44/17.66  Inferencing          : 3.21
% 27.44/17.66  Reduction            : 6.77
% 27.44/17.66  Demodulation         : 5.17
% 27.44/17.66  BG Simplification    : 0.29
% 27.44/17.66  Subsumption          : 5.36
% 27.44/17.66  Abstraction          : 0.57
% 27.44/17.66  MUC search           : 0.00
% 27.44/17.66  Cooper               : 0.00
% 27.44/17.66  Total                : 16.93
% 27.44/17.66  Index Insertion      : 0.00
% 27.44/17.66  Index Deletion       : 0.00
% 27.44/17.66  Index Matching       : 0.00
% 27.44/17.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
