%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:08 EST 2020

% Result     : Theorem 9.32s
% Output     : CNFRefutation 9.44s
% Verified   : 
% Statistics : Number of formulae       :  116 (1026 expanded)
%              Number of leaves         :   36 ( 373 expanded)
%              Depth                    :   24
%              Number of atoms          :  226 (3606 expanded)
%              Number of equality atoms :   36 ( 739 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ! [C] :
            ( ~ v1_xboole_0(C)
           => ! [D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,C)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
               => ( ! [E] :
                      ( m1_subset_1(E,B)
                     => r2_hidden(k3_funct_2(B,C,D,E),A) )
                 => r1_tarski(k2_relset_1(B,C,D),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_75,axiom,(
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

tff(f_105,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_156,plain,(
    ! [A_73,B_74,C_75] :
      ( k2_relset_1(A_73,B_74,C_75) = k2_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_165,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_156])).

tff(c_175,plain,(
    ! [A_76,B_77,C_78] :
      ( m1_subset_1(k2_relset_1(A_76,B_77,C_78),k1_zfmisc_1(B_77))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_193,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_175])).

tff(c_199,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_193])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_203,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_199,c_8])).

tff(c_46,plain,(
    ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_170,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_46])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_52,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_76,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_85,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_76])).

tff(c_146,plain,(
    ! [A_70,B_71,C_72] :
      ( k1_relset_1(A_70,B_71,C_72) = k1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_155,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_146])).

tff(c_9928,plain,(
    ! [B_646,A_647,C_648] :
      ( k1_xboole_0 = B_646
      | k1_relset_1(A_647,B_646,C_648) = A_647
      | ~ v1_funct_2(C_648,A_647,B_646)
      | ~ m1_subset_1(C_648,k1_zfmisc_1(k2_zfmisc_1(A_647,B_646))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_9943,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_9928])).

tff(c_9949,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_155,c_9943])).

tff(c_10043,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_9949])).

tff(c_40,plain,(
    ! [C_30,B_29] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_30),B_29,C_30),k1_relat_1(C_30))
      | v1_funct_2(C_30,k1_relat_1(C_30),B_29)
      | ~ v1_funct_1(C_30)
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_10051,plain,(
    ! [B_29] :
      ( r2_hidden('#skF_1'(k1_relat_1('#skF_5'),B_29,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_29)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10043,c_40])).

tff(c_10289,plain,(
    ! [B_665] :
      ( r2_hidden('#skF_1'('#skF_3',B_665,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_665) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_54,c_10043,c_10043,c_10051])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10293,plain,(
    ! [B_665] :
      ( m1_subset_1('#skF_1'('#skF_3',B_665,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_665) ) ),
    inference(resolution,[status(thm)],[c_10289,c_6])).

tff(c_10449,plain,(
    ! [A_679,B_680,C_681,D_682] :
      ( k3_funct_2(A_679,B_680,C_681,D_682) = k1_funct_1(C_681,D_682)
      | ~ m1_subset_1(D_682,A_679)
      | ~ m1_subset_1(C_681,k1_zfmisc_1(k2_zfmisc_1(A_679,B_680)))
      | ~ v1_funct_2(C_681,A_679,B_680)
      | ~ v1_funct_1(C_681)
      | v1_xboole_0(A_679) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_10453,plain,(
    ! [B_680,C_681,B_665] :
      ( k3_funct_2('#skF_3',B_680,C_681,'#skF_1'('#skF_3',B_665,'#skF_5')) = k1_funct_1(C_681,'#skF_1'('#skF_3',B_665,'#skF_5'))
      | ~ m1_subset_1(C_681,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_680)))
      | ~ v1_funct_2(C_681,'#skF_3',B_680)
      | ~ v1_funct_1(C_681)
      | v1_xboole_0('#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_665) ) ),
    inference(resolution,[status(thm)],[c_10293,c_10449])).

tff(c_10645,plain,(
    ! [B_690,C_691,B_692] :
      ( k3_funct_2('#skF_3',B_690,C_691,'#skF_1'('#skF_3',B_692,'#skF_5')) = k1_funct_1(C_691,'#skF_1'('#skF_3',B_692,'#skF_5'))
      | ~ m1_subset_1(C_691,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_690)))
      | ~ v1_funct_2(C_691,'#skF_3',B_690)
      | ~ v1_funct_1(C_691)
      | v1_funct_2('#skF_5','#skF_3',B_692) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_10453])).

tff(c_10658,plain,(
    ! [B_692] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_692,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_692,'#skF_5'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_funct_2('#skF_5','#skF_3',B_692) ) ),
    inference(resolution,[status(thm)],[c_50,c_10645])).

tff(c_10750,plain,(
    ! [B_702] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_702,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_702,'#skF_5'))
      | v1_funct_2('#skF_5','#skF_3',B_702) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_10658])).

tff(c_48,plain,(
    ! [E_43] :
      ( r2_hidden(k3_funct_2('#skF_3','#skF_4','#skF_5',E_43),'#skF_2')
      | ~ m1_subset_1(E_43,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_10759,plain,(
    ! [B_702] :
      ( r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_702,'#skF_5')),'#skF_2')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_702,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_702) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10750,c_48])).

tff(c_10267,plain,(
    ! [C_661,B_662] :
      ( ~ r2_hidden(k1_funct_1(C_661,'#skF_1'(k1_relat_1(C_661),B_662,C_661)),B_662)
      | v1_funct_2(C_661,k1_relat_1(C_661),B_662)
      | ~ v1_funct_1(C_661)
      | ~ v1_relat_1(C_661) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_10270,plain,(
    ! [B_662] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_662,'#skF_5')),B_662)
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_662)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10043,c_10267])).

tff(c_12990,plain,(
    ! [B_797] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_797,'#skF_5')),B_797)
      | v1_funct_2('#skF_5','#skF_3',B_797) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_54,c_10043,c_10270])).

tff(c_12995,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_10759,c_12990])).

tff(c_13003,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_12995])).

tff(c_10377,plain,(
    ! [C_668,B_669] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_668),B_669,C_668),k1_relat_1(C_668))
      | m1_subset_1(C_668,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_668),B_669)))
      | ~ v1_funct_1(C_668)
      | ~ v1_relat_1(C_668) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_10383,plain,(
    ! [B_669] :
      ( r2_hidden('#skF_1'('#skF_3',B_669,'#skF_5'),k1_relat_1('#skF_5'))
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_669)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10043,c_10377])).

tff(c_12224,plain,(
    ! [B_769] :
      ( r2_hidden('#skF_1'('#skF_3',B_769,'#skF_5'),'#skF_3')
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_769))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_54,c_10043,c_10043,c_10383])).

tff(c_12289,plain,(
    ! [B_771] :
      ( r1_tarski('#skF_5',k2_zfmisc_1('#skF_3',B_771))
      | r2_hidden('#skF_1'('#skF_3',B_771,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12224,c_8])).

tff(c_12293,plain,(
    ! [B_771] :
      ( m1_subset_1('#skF_1'('#skF_3',B_771,'#skF_5'),'#skF_3')
      | r1_tarski('#skF_5',k2_zfmisc_1('#skF_3',B_771)) ) ),
    inference(resolution,[status(thm)],[c_12289,c_6])).

tff(c_11702,plain,(
    ! [C_739,B_740] :
      ( m1_subset_1('#skF_1'(k1_relat_1(C_739),B_740,C_739),k1_relat_1(C_739))
      | m1_subset_1(C_739,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_739),B_740)))
      | ~ v1_funct_1(C_739)
      | ~ v1_relat_1(C_739) ) ),
    inference(resolution,[status(thm)],[c_10377,c_6])).

tff(c_11710,plain,(
    ! [B_740] :
      ( m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),B_740,'#skF_5'),'#skF_3')
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_740)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10043,c_11702])).

tff(c_12919,plain,(
    ! [B_796] :
      ( m1_subset_1('#skF_1'('#skF_3',B_796,'#skF_5'),'#skF_3')
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_796))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_54,c_10043,c_10043,c_11710])).

tff(c_18,plain,(
    ! [A_18,B_19,C_20] :
      ( k2_relset_1(A_18,B_19,C_20) = k2_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_13081,plain,(
    ! [B_804] :
      ( k2_relset_1('#skF_3',B_804,'#skF_5') = k2_relat_1('#skF_5')
      | m1_subset_1('#skF_1'('#skF_3',B_804,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12919,c_18])).

tff(c_13087,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_13081,c_13003])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10559,plain,(
    ! [A_686,B_687,C_688] :
      ( r1_tarski(k2_relset_1(A_686,B_687,C_688),B_687)
      | ~ m1_subset_1(C_688,k1_zfmisc_1(k2_zfmisc_1(A_686,B_687))) ) ),
    inference(resolution,[status(thm)],[c_175,c_8])).

tff(c_10574,plain,(
    ! [A_686,B_687,A_7] :
      ( r1_tarski(k2_relset_1(A_686,B_687,A_7),B_687)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_686,B_687)) ) ),
    inference(resolution,[status(thm)],[c_10,c_10559])).

tff(c_13107,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),'#skF_2')
    | ~ r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13087,c_10574])).

tff(c_13113,plain,(
    ~ r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_13107])).

tff(c_13117,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_12293,c_13113])).

tff(c_13121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13003,c_13117])).

tff(c_13123,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_12995])).

tff(c_32,plain,(
    ! [A_24,B_25,C_26,D_27] :
      ( k3_funct_2(A_24,B_25,C_26,D_27) = k1_funct_1(C_26,D_27)
      | ~ m1_subset_1(D_27,A_24)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ v1_funct_2(C_26,A_24,B_25)
      | ~ v1_funct_1(C_26)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_13163,plain,(
    ! [B_25,C_26] :
      ( k3_funct_2('#skF_3',B_25,C_26,'#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1(C_26,'#skF_1'('#skF_3','#skF_2','#skF_5'))
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_25)))
      | ~ v1_funct_2(C_26,'#skF_3',B_25)
      | ~ v1_funct_1(C_26)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_13123,c_32])).

tff(c_13665,plain,(
    ! [B_820,C_821] :
      ( k3_funct_2('#skF_3',B_820,C_821,'#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1(C_821,'#skF_1'('#skF_3','#skF_2','#skF_5'))
      | ~ m1_subset_1(C_821,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_820)))
      | ~ v1_funct_2(C_821,'#skF_3',B_820)
      | ~ v1_funct_1(C_821) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_13163])).

tff(c_13689,plain,
    ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5'))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_13665])).

tff(c_13702,plain,(
    k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_13689])).

tff(c_14685,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13702,c_48])).

tff(c_14696,plain,(
    r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13123,c_14685])).

tff(c_10433,plain,(
    ! [C_677,B_678] :
      ( ~ r2_hidden(k1_funct_1(C_677,'#skF_1'(k1_relat_1(C_677),B_678,C_677)),B_678)
      | m1_subset_1(C_677,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_677),B_678)))
      | ~ v1_funct_1(C_677)
      | ~ v1_relat_1(C_677) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_10436,plain,(
    ! [B_678] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_678,'#skF_5')),B_678)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_678)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10043,c_10433])).

tff(c_10438,plain,(
    ! [B_678] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_678,'#skF_5')),B_678)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_678))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_54,c_10043,c_10436])).

tff(c_14713,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_14696,c_10438])).

tff(c_14780,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_14713,c_18])).

tff(c_197,plain,(
    ! [A_76,B_77,C_78] :
      ( r1_tarski(k2_relset_1(A_76,B_77,C_78),B_77)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(resolution,[status(thm)],[c_175,c_8])).

tff(c_14773,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_2','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_14713,c_197])).

tff(c_15141,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14780,c_14773])).

tff(c_15143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_15141])).

tff(c_15144,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9949])).

tff(c_4,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_97,plain,(
    ! [A_58,C_59,B_60] :
      ( r1_tarski(A_58,C_59)
      | ~ r1_tarski(B_60,C_59)
      | ~ r1_tarski(A_58,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_103,plain,(
    ! [A_58,A_4] :
      ( r1_tarski(A_58,A_4)
      | ~ r1_tarski(A_58,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_97])).

tff(c_15394,plain,(
    ! [A_870,A_871] :
      ( r1_tarski(A_870,A_871)
      | ~ r1_tarski(A_870,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15144,c_103])).

tff(c_15407,plain,(
    ! [A_871] : r1_tarski(k2_relat_1('#skF_5'),A_871) ),
    inference(resolution,[status(thm)],[c_203,c_15394])).

tff(c_15413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15407,c_170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:25:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.32/3.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.32/3.53  
% 9.32/3.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.32/3.53  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 9.32/3.53  
% 9.32/3.53  %Foreground sorts:
% 9.32/3.53  
% 9.32/3.53  
% 9.32/3.53  %Background operators:
% 9.32/3.53  
% 9.32/3.53  
% 9.32/3.53  %Foreground operators:
% 9.32/3.53  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.32/3.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.32/3.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.32/3.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.32/3.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.32/3.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.32/3.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.32/3.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.32/3.53  tff('#skF_5', type, '#skF_5': $i).
% 9.32/3.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.32/3.53  tff('#skF_2', type, '#skF_2': $i).
% 9.32/3.53  tff('#skF_3', type, '#skF_3': $i).
% 9.32/3.53  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.32/3.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.32/3.53  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.32/3.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.32/3.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.32/3.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.32/3.53  tff('#skF_4', type, '#skF_4': $i).
% 9.32/3.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.32/3.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.32/3.53  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 9.32/3.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.32/3.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.32/3.53  
% 9.44/3.55  tff(f_127, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_funct_2)).
% 9.44/3.55  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.44/3.55  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 9.44/3.55  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.44/3.55  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.44/3.55  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.44/3.55  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.44/3.55  tff(f_105, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 9.44/3.55  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 9.44/3.55  tff(f_88, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 9.44/3.55  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.44/3.55  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 9.44/3.55  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.44/3.55  tff(c_156, plain, (![A_73, B_74, C_75]: (k2_relset_1(A_73, B_74, C_75)=k2_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.44/3.55  tff(c_165, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_156])).
% 9.44/3.55  tff(c_175, plain, (![A_76, B_77, C_78]: (m1_subset_1(k2_relset_1(A_76, B_77, C_78), k1_zfmisc_1(B_77)) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.44/3.55  tff(c_193, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_165, c_175])).
% 9.44/3.55  tff(c_199, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_193])).
% 9.44/3.55  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.44/3.55  tff(c_203, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_199, c_8])).
% 9.44/3.55  tff(c_46, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.44/3.55  tff(c_170, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_165, c_46])).
% 9.44/3.55  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.44/3.55  tff(c_52, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.44/3.55  tff(c_58, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.44/3.55  tff(c_76, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.44/3.55  tff(c_85, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_76])).
% 9.44/3.55  tff(c_146, plain, (![A_70, B_71, C_72]: (k1_relset_1(A_70, B_71, C_72)=k1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.44/3.55  tff(c_155, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_146])).
% 9.44/3.55  tff(c_9928, plain, (![B_646, A_647, C_648]: (k1_xboole_0=B_646 | k1_relset_1(A_647, B_646, C_648)=A_647 | ~v1_funct_2(C_648, A_647, B_646) | ~m1_subset_1(C_648, k1_zfmisc_1(k2_zfmisc_1(A_647, B_646))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.44/3.55  tff(c_9943, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_9928])).
% 9.44/3.55  tff(c_9949, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_155, c_9943])).
% 9.44/3.55  tff(c_10043, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_9949])).
% 9.44/3.55  tff(c_40, plain, (![C_30, B_29]: (r2_hidden('#skF_1'(k1_relat_1(C_30), B_29, C_30), k1_relat_1(C_30)) | v1_funct_2(C_30, k1_relat_1(C_30), B_29) | ~v1_funct_1(C_30) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.44/3.55  tff(c_10051, plain, (![B_29]: (r2_hidden('#skF_1'(k1_relat_1('#skF_5'), B_29, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_29) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_10043, c_40])).
% 9.44/3.55  tff(c_10289, plain, (![B_665]: (r2_hidden('#skF_1'('#skF_3', B_665, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_665))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_54, c_10043, c_10043, c_10051])).
% 9.44/3.55  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.44/3.55  tff(c_10293, plain, (![B_665]: (m1_subset_1('#skF_1'('#skF_3', B_665, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_665))), inference(resolution, [status(thm)], [c_10289, c_6])).
% 9.44/3.55  tff(c_10449, plain, (![A_679, B_680, C_681, D_682]: (k3_funct_2(A_679, B_680, C_681, D_682)=k1_funct_1(C_681, D_682) | ~m1_subset_1(D_682, A_679) | ~m1_subset_1(C_681, k1_zfmisc_1(k2_zfmisc_1(A_679, B_680))) | ~v1_funct_2(C_681, A_679, B_680) | ~v1_funct_1(C_681) | v1_xboole_0(A_679))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.44/3.55  tff(c_10453, plain, (![B_680, C_681, B_665]: (k3_funct_2('#skF_3', B_680, C_681, '#skF_1'('#skF_3', B_665, '#skF_5'))=k1_funct_1(C_681, '#skF_1'('#skF_3', B_665, '#skF_5')) | ~m1_subset_1(C_681, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_680))) | ~v1_funct_2(C_681, '#skF_3', B_680) | ~v1_funct_1(C_681) | v1_xboole_0('#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_665))), inference(resolution, [status(thm)], [c_10293, c_10449])).
% 9.44/3.55  tff(c_10645, plain, (![B_690, C_691, B_692]: (k3_funct_2('#skF_3', B_690, C_691, '#skF_1'('#skF_3', B_692, '#skF_5'))=k1_funct_1(C_691, '#skF_1'('#skF_3', B_692, '#skF_5')) | ~m1_subset_1(C_691, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_690))) | ~v1_funct_2(C_691, '#skF_3', B_690) | ~v1_funct_1(C_691) | v1_funct_2('#skF_5', '#skF_3', B_692))), inference(negUnitSimplification, [status(thm)], [c_58, c_10453])).
% 9.44/3.55  tff(c_10658, plain, (![B_692]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_692, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_692, '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_funct_2('#skF_5', '#skF_3', B_692))), inference(resolution, [status(thm)], [c_50, c_10645])).
% 9.44/3.55  tff(c_10750, plain, (![B_702]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_702, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_702, '#skF_5')) | v1_funct_2('#skF_5', '#skF_3', B_702))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_10658])).
% 9.44/3.55  tff(c_48, plain, (![E_43]: (r2_hidden(k3_funct_2('#skF_3', '#skF_4', '#skF_5', E_43), '#skF_2') | ~m1_subset_1(E_43, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.44/3.55  tff(c_10759, plain, (![B_702]: (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_702, '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', B_702, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_702))), inference(superposition, [status(thm), theory('equality')], [c_10750, c_48])).
% 9.44/3.55  tff(c_10267, plain, (![C_661, B_662]: (~r2_hidden(k1_funct_1(C_661, '#skF_1'(k1_relat_1(C_661), B_662, C_661)), B_662) | v1_funct_2(C_661, k1_relat_1(C_661), B_662) | ~v1_funct_1(C_661) | ~v1_relat_1(C_661))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.44/3.55  tff(c_10270, plain, (![B_662]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_662, '#skF_5')), B_662) | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_662) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_10043, c_10267])).
% 9.44/3.55  tff(c_12990, plain, (![B_797]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_797, '#skF_5')), B_797) | v1_funct_2('#skF_5', '#skF_3', B_797))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_54, c_10043, c_10270])).
% 9.44/3.55  tff(c_12995, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_10759, c_12990])).
% 9.44/3.55  tff(c_13003, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_12995])).
% 9.44/3.55  tff(c_10377, plain, (![C_668, B_669]: (r2_hidden('#skF_1'(k1_relat_1(C_668), B_669, C_668), k1_relat_1(C_668)) | m1_subset_1(C_668, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_668), B_669))) | ~v1_funct_1(C_668) | ~v1_relat_1(C_668))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.44/3.55  tff(c_10383, plain, (![B_669]: (r2_hidden('#skF_1'('#skF_3', B_669, '#skF_5'), k1_relat_1('#skF_5')) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_669))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_10043, c_10377])).
% 9.44/3.55  tff(c_12224, plain, (![B_769]: (r2_hidden('#skF_1'('#skF_3', B_769, '#skF_5'), '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_769))))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_54, c_10043, c_10043, c_10383])).
% 9.44/3.55  tff(c_12289, plain, (![B_771]: (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', B_771)) | r2_hidden('#skF_1'('#skF_3', B_771, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_12224, c_8])).
% 9.44/3.55  tff(c_12293, plain, (![B_771]: (m1_subset_1('#skF_1'('#skF_3', B_771, '#skF_5'), '#skF_3') | r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', B_771)))), inference(resolution, [status(thm)], [c_12289, c_6])).
% 9.44/3.55  tff(c_11702, plain, (![C_739, B_740]: (m1_subset_1('#skF_1'(k1_relat_1(C_739), B_740, C_739), k1_relat_1(C_739)) | m1_subset_1(C_739, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_739), B_740))) | ~v1_funct_1(C_739) | ~v1_relat_1(C_739))), inference(resolution, [status(thm)], [c_10377, c_6])).
% 9.44/3.55  tff(c_11710, plain, (![B_740]: (m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), B_740, '#skF_5'), '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_740))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_10043, c_11702])).
% 9.44/3.55  tff(c_12919, plain, (![B_796]: (m1_subset_1('#skF_1'('#skF_3', B_796, '#skF_5'), '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_796))))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_54, c_10043, c_10043, c_11710])).
% 9.44/3.55  tff(c_18, plain, (![A_18, B_19, C_20]: (k2_relset_1(A_18, B_19, C_20)=k2_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.44/3.55  tff(c_13081, plain, (![B_804]: (k2_relset_1('#skF_3', B_804, '#skF_5')=k2_relat_1('#skF_5') | m1_subset_1('#skF_1'('#skF_3', B_804, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_12919, c_18])).
% 9.44/3.55  tff(c_13087, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_13081, c_13003])).
% 9.44/3.55  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.44/3.55  tff(c_10559, plain, (![A_686, B_687, C_688]: (r1_tarski(k2_relset_1(A_686, B_687, C_688), B_687) | ~m1_subset_1(C_688, k1_zfmisc_1(k2_zfmisc_1(A_686, B_687))))), inference(resolution, [status(thm)], [c_175, c_8])).
% 9.44/3.55  tff(c_10574, plain, (![A_686, B_687, A_7]: (r1_tarski(k2_relset_1(A_686, B_687, A_7), B_687) | ~r1_tarski(A_7, k2_zfmisc_1(A_686, B_687)))), inference(resolution, [status(thm)], [c_10, c_10559])).
% 9.44/3.55  tff(c_13107, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_2') | ~r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_13087, c_10574])).
% 9.44/3.55  tff(c_13113, plain, (~r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_170, c_13107])).
% 9.44/3.55  tff(c_13117, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_12293, c_13113])).
% 9.44/3.55  tff(c_13121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13003, c_13117])).
% 9.44/3.55  tff(c_13123, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_12995])).
% 9.44/3.55  tff(c_32, plain, (![A_24, B_25, C_26, D_27]: (k3_funct_2(A_24, B_25, C_26, D_27)=k1_funct_1(C_26, D_27) | ~m1_subset_1(D_27, A_24) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~v1_funct_2(C_26, A_24, B_25) | ~v1_funct_1(C_26) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.44/3.55  tff(c_13163, plain, (![B_25, C_26]: (k3_funct_2('#skF_3', B_25, C_26, '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1(C_26, '#skF_1'('#skF_3', '#skF_2', '#skF_5')) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_25))) | ~v1_funct_2(C_26, '#skF_3', B_25) | ~v1_funct_1(C_26) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_13123, c_32])).
% 9.44/3.55  tff(c_13665, plain, (![B_820, C_821]: (k3_funct_2('#skF_3', B_820, C_821, '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1(C_821, '#skF_1'('#skF_3', '#skF_2', '#skF_5')) | ~m1_subset_1(C_821, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_820))) | ~v1_funct_2(C_821, '#skF_3', B_820) | ~v1_funct_1(C_821))), inference(negUnitSimplification, [status(thm)], [c_58, c_13163])).
% 9.44/3.55  tff(c_13689, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_13665])).
% 9.44/3.55  tff(c_13702, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_13689])).
% 9.44/3.55  tff(c_14685, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13702, c_48])).
% 9.44/3.55  tff(c_14696, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13123, c_14685])).
% 9.44/3.55  tff(c_10433, plain, (![C_677, B_678]: (~r2_hidden(k1_funct_1(C_677, '#skF_1'(k1_relat_1(C_677), B_678, C_677)), B_678) | m1_subset_1(C_677, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_677), B_678))) | ~v1_funct_1(C_677) | ~v1_relat_1(C_677))), inference(cnfTransformation, [status(thm)], [f_105])).
% 9.44/3.55  tff(c_10436, plain, (![B_678]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_678, '#skF_5')), B_678) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_678))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_10043, c_10433])).
% 9.44/3.55  tff(c_10438, plain, (![B_678]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_678, '#skF_5')), B_678) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_678))))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_54, c_10043, c_10436])).
% 9.44/3.55  tff(c_14713, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_14696, c_10438])).
% 9.44/3.55  tff(c_14780, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_14713, c_18])).
% 9.44/3.55  tff(c_197, plain, (![A_76, B_77, C_78]: (r1_tarski(k2_relset_1(A_76, B_77, C_78), B_77) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(resolution, [status(thm)], [c_175, c_8])).
% 9.44/3.55  tff(c_14773, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_2', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_14713, c_197])).
% 9.44/3.55  tff(c_15141, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14780, c_14773])).
% 9.44/3.55  tff(c_15143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_170, c_15141])).
% 9.44/3.55  tff(c_15144, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_9949])).
% 9.44/3.55  tff(c_4, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.44/3.55  tff(c_97, plain, (![A_58, C_59, B_60]: (r1_tarski(A_58, C_59) | ~r1_tarski(B_60, C_59) | ~r1_tarski(A_58, B_60))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.44/3.55  tff(c_103, plain, (![A_58, A_4]: (r1_tarski(A_58, A_4) | ~r1_tarski(A_58, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_97])).
% 9.44/3.55  tff(c_15394, plain, (![A_870, A_871]: (r1_tarski(A_870, A_871) | ~r1_tarski(A_870, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_15144, c_103])).
% 9.44/3.55  tff(c_15407, plain, (![A_871]: (r1_tarski(k2_relat_1('#skF_5'), A_871))), inference(resolution, [status(thm)], [c_203, c_15394])).
% 9.44/3.55  tff(c_15413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15407, c_170])).
% 9.44/3.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.44/3.55  
% 9.44/3.55  Inference rules
% 9.44/3.55  ----------------------
% 9.44/3.55  #Ref     : 0
% 9.44/3.55  #Sup     : 3233
% 9.44/3.55  #Fact    : 0
% 9.44/3.55  #Define  : 0
% 9.44/3.55  #Split   : 55
% 9.44/3.55  #Chain   : 0
% 9.44/3.55  #Close   : 0
% 9.44/3.55  
% 9.44/3.55  Ordering : KBO
% 9.44/3.55  
% 9.44/3.55  Simplification rules
% 9.44/3.55  ----------------------
% 9.44/3.55  #Subsume      : 499
% 9.44/3.55  #Demod        : 2392
% 9.44/3.55  #Tautology    : 1096
% 9.44/3.55  #SimpNegUnit  : 107
% 9.44/3.55  #BackRed      : 208
% 9.44/3.55  
% 9.44/3.55  #Partial instantiations: 0
% 9.44/3.55  #Strategies tried      : 1
% 9.44/3.55  
% 9.44/3.55  Timing (in seconds)
% 9.44/3.55  ----------------------
% 9.44/3.56  Preprocessing        : 0.32
% 9.44/3.56  Parsing              : 0.16
% 9.44/3.56  CNF conversion       : 0.02
% 9.44/3.56  Main loop            : 2.41
% 9.44/3.56  Inferencing          : 0.72
% 9.44/3.56  Reduction            : 0.86
% 9.44/3.56  Demodulation         : 0.60
% 9.44/3.56  BG Simplification    : 0.08
% 9.44/3.56  Subsumption          : 0.54
% 9.44/3.56  Abstraction          : 0.11
% 9.44/3.56  MUC search           : 0.00
% 9.44/3.56  Cooper               : 0.00
% 9.44/3.56  Total                : 2.77
% 9.44/3.56  Index Insertion      : 0.00
% 9.44/3.56  Index Deletion       : 0.00
% 9.44/3.56  Index Matching       : 0.00
% 9.44/3.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
