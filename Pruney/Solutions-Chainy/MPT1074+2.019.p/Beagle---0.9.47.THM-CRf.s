%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:08 EST 2020

% Result     : Theorem 10.90s
% Output     : CNFRefutation 11.04s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 556 expanded)
%              Number of leaves         :   35 ( 206 expanded)
%              Depth                    :   24
%              Number of atoms          :  227 (2079 expanded)
%              Number of equality atoms :   20 ( 102 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
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

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_94,axiom,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_145,plain,(
    ! [A_76,B_77,C_78] :
      ( k2_relset_1(A_76,B_77,C_78) = k2_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_154,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_145])).

tff(c_38,plain,(
    ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_155,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_38])).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_63,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_69,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_63])).

tff(c_73,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_69])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_82,plain,(
    ! [C_55,A_56,B_57] :
      ( v4_relat_1(C_55,A_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_91,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_82])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_44,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_321,plain,(
    ! [C_104,B_105] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_104),B_105,C_104),k1_relat_1(C_104))
      | v1_funct_2(C_104,k1_relat_1(C_104),B_105)
      | ~ v1_funct_1(C_104)
      | ~ v1_relat_1(C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_133,plain,(
    ! [A_69,C_70,B_71] :
      ( m1_subset_1(A_69,C_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(C_70))
      | ~ r2_hidden(A_69,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_138,plain,(
    ! [A_69,B_2,A_1] :
      ( m1_subset_1(A_69,B_2)
      | ~ r2_hidden(A_69,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_133])).

tff(c_324,plain,(
    ! [C_104,B_105,B_2] :
      ( m1_subset_1('#skF_1'(k1_relat_1(C_104),B_105,C_104),B_2)
      | ~ r1_tarski(k1_relat_1(C_104),B_2)
      | v1_funct_2(C_104,k1_relat_1(C_104),B_105)
      | ~ v1_funct_1(C_104)
      | ~ v1_relat_1(C_104) ) ),
    inference(resolution,[status(thm)],[c_321,c_138])).

tff(c_545,plain,(
    ! [A_175,B_176,C_177,D_178] :
      ( k3_funct_2(A_175,B_176,C_177,D_178) = k1_funct_1(C_177,D_178)
      | ~ m1_subset_1(D_178,A_175)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176)))
      | ~ v1_funct_2(C_177,A_175,B_176)
      | ~ v1_funct_1(C_177)
      | v1_xboole_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8549,plain,(
    ! [C_1227,B_1231,C_1229,B_1230,B_1228] :
      ( k3_funct_2(B_1231,B_1230,C_1227,'#skF_1'(k1_relat_1(C_1229),B_1228,C_1229)) = k1_funct_1(C_1227,'#skF_1'(k1_relat_1(C_1229),B_1228,C_1229))
      | ~ m1_subset_1(C_1227,k1_zfmisc_1(k2_zfmisc_1(B_1231,B_1230)))
      | ~ v1_funct_2(C_1227,B_1231,B_1230)
      | ~ v1_funct_1(C_1227)
      | v1_xboole_0(B_1231)
      | ~ r1_tarski(k1_relat_1(C_1229),B_1231)
      | v1_funct_2(C_1229,k1_relat_1(C_1229),B_1228)
      | ~ v1_funct_1(C_1229)
      | ~ v1_relat_1(C_1229) ) ),
    inference(resolution,[status(thm)],[c_324,c_545])).

tff(c_8617,plain,(
    ! [C_1229,B_1228] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'(k1_relat_1(C_1229),B_1228,C_1229)) = k1_funct_1('#skF_5','#skF_1'(k1_relat_1(C_1229),B_1228,C_1229))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_3')
      | ~ r1_tarski(k1_relat_1(C_1229),'#skF_3')
      | v1_funct_2(C_1229,k1_relat_1(C_1229),B_1228)
      | ~ v1_funct_1(C_1229)
      | ~ v1_relat_1(C_1229) ) ),
    inference(resolution,[status(thm)],[c_42,c_8549])).

tff(c_8643,plain,(
    ! [C_1229,B_1228] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'(k1_relat_1(C_1229),B_1228,C_1229)) = k1_funct_1('#skF_5','#skF_1'(k1_relat_1(C_1229),B_1228,C_1229))
      | v1_xboole_0('#skF_3')
      | ~ r1_tarski(k1_relat_1(C_1229),'#skF_3')
      | v1_funct_2(C_1229,k1_relat_1(C_1229),B_1228)
      | ~ v1_funct_1(C_1229)
      | ~ v1_relat_1(C_1229) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_8617])).

tff(c_8645,plain,(
    ! [C_1232,B_1233] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'(k1_relat_1(C_1232),B_1233,C_1232)) = k1_funct_1('#skF_5','#skF_1'(k1_relat_1(C_1232),B_1233,C_1232))
      | ~ r1_tarski(k1_relat_1(C_1232),'#skF_3')
      | v1_funct_2(C_1232,k1_relat_1(C_1232),B_1233)
      | ~ v1_funct_1(C_1232)
      | ~ v1_relat_1(C_1232) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_8643])).

tff(c_40,plain,(
    ! [E_41] :
      ( r2_hidden(k3_funct_2('#skF_3','#skF_4','#skF_5',E_41),'#skF_2')
      | ~ m1_subset_1(E_41,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_8712,plain,(
    ! [C_1234,B_1235] :
      ( r2_hidden(k1_funct_1('#skF_5','#skF_1'(k1_relat_1(C_1234),B_1235,C_1234)),'#skF_2')
      | ~ m1_subset_1('#skF_1'(k1_relat_1(C_1234),B_1235,C_1234),'#skF_3')
      | ~ r1_tarski(k1_relat_1(C_1234),'#skF_3')
      | v1_funct_2(C_1234,k1_relat_1(C_1234),B_1235)
      | ~ v1_funct_1(C_1234)
      | ~ v1_relat_1(C_1234) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8645,c_40])).

tff(c_30,plain,(
    ! [C_28,B_27] :
      ( ~ r2_hidden(k1_funct_1(C_28,'#skF_1'(k1_relat_1(C_28),B_27,C_28)),B_27)
      | v1_funct_2(C_28,k1_relat_1(C_28),B_27)
      | ~ v1_funct_1(C_28)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_8720,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_8712,c_30])).

tff(c_8728,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_46,c_8720])).

tff(c_8730,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_8728])).

tff(c_8815,plain,
    ( ~ v4_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_8730])).

tff(c_8819,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_91,c_8815])).

tff(c_8821,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_8728])).

tff(c_424,plain,(
    ! [C_150,B_151] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_150),B_151,C_150),k1_relat_1(C_150))
      | m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_150),B_151)))
      | ~ v1_funct_1(C_150)
      | ~ v1_relat_1(C_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_592,plain,(
    ! [C_182,B_183,B_184] :
      ( m1_subset_1('#skF_1'(k1_relat_1(C_182),B_183,C_182),B_184)
      | ~ r1_tarski(k1_relat_1(C_182),B_184)
      | m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_182),B_183)))
      | ~ v1_funct_1(C_182)
      | ~ v1_relat_1(C_182) ) ),
    inference(resolution,[status(thm)],[c_424,c_138])).

tff(c_22,plain,(
    ! [A_19,B_20,C_21] :
      ( k2_relset_1(A_19,B_20,C_21) = k2_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_685,plain,(
    ! [C_182,B_183,B_184] :
      ( k2_relset_1(k1_relat_1(C_182),B_183,C_182) = k2_relat_1(C_182)
      | m1_subset_1('#skF_1'(k1_relat_1(C_182),B_183,C_182),B_184)
      | ~ r1_tarski(k1_relat_1(C_182),B_184)
      | ~ v1_funct_1(C_182)
      | ~ v1_relat_1(C_182) ) ),
    inference(resolution,[status(thm)],[c_592,c_22])).

tff(c_8820,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3')
    | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_8728])).

tff(c_8832,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_8820])).

tff(c_8845,plain,
    ( k2_relset_1(k1_relat_1('#skF_5'),'#skF_2','#skF_5') = k2_relat_1('#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_685,c_8832])).

tff(c_8868,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),'#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_46,c_8821,c_8845])).

tff(c_210,plain,(
    ! [A_92,B_93,C_94] :
      ( m1_subset_1(k2_relset_1(A_92,B_93,C_94),k1_zfmisc_1(B_93))
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_239,plain,(
    ! [A_92,B_93,C_94] :
      ( r1_tarski(k2_relset_1(A_92,B_93,C_94),B_93)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(resolution,[status(thm)],[c_210,c_2])).

tff(c_684,plain,(
    ! [C_182,B_183,B_184] :
      ( r1_tarski(k2_relset_1(k1_relat_1(C_182),B_183,C_182),B_183)
      | m1_subset_1('#skF_1'(k1_relat_1(C_182),B_183,C_182),B_184)
      | ~ r1_tarski(k1_relat_1(C_182),B_184)
      | ~ v1_funct_1(C_182)
      | ~ v1_relat_1(C_182) ) ),
    inference(resolution,[status(thm)],[c_592,c_239])).

tff(c_8938,plain,(
    ! [B_184] :
      ( r1_tarski(k2_relat_1('#skF_5'),'#skF_2')
      | m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),B_184)
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_184)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8868,c_684])).

tff(c_8954,plain,(
    ! [B_184] :
      ( r1_tarski(k2_relat_1('#skF_5'),'#skF_2')
      | m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),B_184)
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_46,c_8938])).

tff(c_8970,plain,(
    ! [B_1245] :
      ( m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),B_1245)
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_1245) ) ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_8954])).

tff(c_8973,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_8970,c_8832])).

tff(c_9039,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8821,c_8973])).

tff(c_9041,plain,(
    m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_8820])).

tff(c_24,plain,(
    ! [A_22,B_23,C_24,D_25] :
      ( k3_funct_2(A_22,B_23,C_24,D_25) = k1_funct_1(C_24,D_25)
      | ~ m1_subset_1(D_25,A_22)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2(C_24,A_22,B_23)
      | ~ v1_funct_1(C_24)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_9085,plain,(
    ! [B_23,C_24] :
      ( k3_funct_2('#skF_3',B_23,C_24,'#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')) = k1_funct_1(C_24,'#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_23)))
      | ~ v1_funct_2(C_24,'#skF_3',B_23)
      | ~ v1_funct_1(C_24)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_9041,c_24])).

tff(c_9176,plain,(
    ! [B_1256,C_1257] :
      ( k3_funct_2('#skF_3',B_1256,C_1257,'#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')) = k1_funct_1(C_1257,'#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'))
      | ~ m1_subset_1(C_1257,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_1256)))
      | ~ v1_funct_2(C_1257,'#skF_3',B_1256)
      | ~ v1_funct_1(C_1257) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_9085])).

tff(c_9259,plain,
    ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_9176])).

tff(c_9282,plain,(
    k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_9259])).

tff(c_9344,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')),'#skF_2')
    | ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9282,c_40])).

tff(c_9392,plain,(
    r2_hidden(k1_funct_1('#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9041,c_9344])).

tff(c_26,plain,(
    ! [C_28,B_27] :
      ( ~ r2_hidden(k1_funct_1(C_28,'#skF_1'(k1_relat_1(C_28),B_27,C_28)),B_27)
      | m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_28),B_27)))
      | ~ v1_funct_1(C_28)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_9399,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_9392,c_26])).

tff(c_9407,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_46,c_9399])).

tff(c_9459,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_9407,c_2])).

tff(c_9452,plain,(
    k2_relset_1(k1_relat_1('#skF_5'),'#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_9407,c_22])).

tff(c_279,plain,(
    ! [A_98,B_99,C_100] :
      ( r1_tarski(k2_relset_1(A_98,B_99,C_100),B_99)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(resolution,[status(thm)],[c_210,c_2])).

tff(c_293,plain,(
    ! [A_98,B_99,A_1] :
      ( r1_tarski(k2_relset_1(A_98,B_99,A_1),B_99)
      | ~ r1_tarski(A_1,k2_zfmisc_1(A_98,B_99)) ) ),
    inference(resolution,[status(thm)],[c_4,c_279])).

tff(c_9517,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),'#skF_2')
    | ~ r1_tarski('#skF_5',k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9452,c_293])).

tff(c_9534,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9459,c_9517])).

tff(c_9536,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_9534])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:53:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.90/4.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.90/4.50  
% 10.90/4.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.90/4.50  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 10.90/4.50  
% 10.90/4.50  %Foreground sorts:
% 10.90/4.50  
% 10.90/4.50  
% 10.90/4.50  %Background operators:
% 10.90/4.50  
% 10.90/4.50  
% 10.90/4.50  %Foreground operators:
% 10.90/4.50  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.90/4.50  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.90/4.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.90/4.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.90/4.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.90/4.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.90/4.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.90/4.50  tff('#skF_5', type, '#skF_5': $i).
% 10.90/4.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.90/4.50  tff('#skF_2', type, '#skF_2': $i).
% 10.90/4.50  tff('#skF_3', type, '#skF_3': $i).
% 10.90/4.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.90/4.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.90/4.50  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.90/4.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.90/4.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.90/4.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.90/4.50  tff('#skF_4', type, '#skF_4': $i).
% 10.90/4.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.90/4.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.90/4.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.90/4.50  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 10.90/4.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.90/4.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.90/4.50  
% 11.04/4.52  tff(f_116, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_funct_2)).
% 11.04/4.52  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.04/4.52  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 11.04/4.52  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 11.04/4.52  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.04/4.52  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 11.04/4.52  tff(f_94, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 11.04/4.52  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.04/4.52  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 11.04/4.52  tff(f_77, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 11.04/4.52  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 11.04/4.52  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 11.04/4.52  tff(c_145, plain, (![A_76, B_77, C_78]: (k2_relset_1(A_76, B_77, C_78)=k2_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.04/4.52  tff(c_154, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_145])).
% 11.04/4.52  tff(c_38, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 11.04/4.52  tff(c_155, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_38])).
% 11.04/4.52  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.04/4.52  tff(c_63, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.04/4.52  tff(c_69, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_63])).
% 11.04/4.52  tff(c_73, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_69])).
% 11.04/4.52  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 11.04/4.52  tff(c_82, plain, (![C_55, A_56, B_57]: (v4_relat_1(C_55, A_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.04/4.52  tff(c_91, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_82])).
% 11.04/4.52  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(B_10), A_9) | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.04/4.52  tff(c_50, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 11.04/4.52  tff(c_44, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 11.04/4.52  tff(c_321, plain, (![C_104, B_105]: (r2_hidden('#skF_1'(k1_relat_1(C_104), B_105, C_104), k1_relat_1(C_104)) | v1_funct_2(C_104, k1_relat_1(C_104), B_105) | ~v1_funct_1(C_104) | ~v1_relat_1(C_104))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.04/4.52  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.04/4.52  tff(c_133, plain, (![A_69, C_70, B_71]: (m1_subset_1(A_69, C_70) | ~m1_subset_1(B_71, k1_zfmisc_1(C_70)) | ~r2_hidden(A_69, B_71))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.04/4.52  tff(c_138, plain, (![A_69, B_2, A_1]: (m1_subset_1(A_69, B_2) | ~r2_hidden(A_69, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_133])).
% 11.04/4.52  tff(c_324, plain, (![C_104, B_105, B_2]: (m1_subset_1('#skF_1'(k1_relat_1(C_104), B_105, C_104), B_2) | ~r1_tarski(k1_relat_1(C_104), B_2) | v1_funct_2(C_104, k1_relat_1(C_104), B_105) | ~v1_funct_1(C_104) | ~v1_relat_1(C_104))), inference(resolution, [status(thm)], [c_321, c_138])).
% 11.04/4.52  tff(c_545, plain, (![A_175, B_176, C_177, D_178]: (k3_funct_2(A_175, B_176, C_177, D_178)=k1_funct_1(C_177, D_178) | ~m1_subset_1(D_178, A_175) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))) | ~v1_funct_2(C_177, A_175, B_176) | ~v1_funct_1(C_177) | v1_xboole_0(A_175))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.04/4.52  tff(c_8549, plain, (![C_1227, B_1231, C_1229, B_1230, B_1228]: (k3_funct_2(B_1231, B_1230, C_1227, '#skF_1'(k1_relat_1(C_1229), B_1228, C_1229))=k1_funct_1(C_1227, '#skF_1'(k1_relat_1(C_1229), B_1228, C_1229)) | ~m1_subset_1(C_1227, k1_zfmisc_1(k2_zfmisc_1(B_1231, B_1230))) | ~v1_funct_2(C_1227, B_1231, B_1230) | ~v1_funct_1(C_1227) | v1_xboole_0(B_1231) | ~r1_tarski(k1_relat_1(C_1229), B_1231) | v1_funct_2(C_1229, k1_relat_1(C_1229), B_1228) | ~v1_funct_1(C_1229) | ~v1_relat_1(C_1229))), inference(resolution, [status(thm)], [c_324, c_545])).
% 11.04/4.52  tff(c_8617, plain, (![C_1229, B_1228]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'(k1_relat_1(C_1229), B_1228, C_1229))=k1_funct_1('#skF_5', '#skF_1'(k1_relat_1(C_1229), B_1228, C_1229)) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3') | ~r1_tarski(k1_relat_1(C_1229), '#skF_3') | v1_funct_2(C_1229, k1_relat_1(C_1229), B_1228) | ~v1_funct_1(C_1229) | ~v1_relat_1(C_1229))), inference(resolution, [status(thm)], [c_42, c_8549])).
% 11.04/4.52  tff(c_8643, plain, (![C_1229, B_1228]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'(k1_relat_1(C_1229), B_1228, C_1229))=k1_funct_1('#skF_5', '#skF_1'(k1_relat_1(C_1229), B_1228, C_1229)) | v1_xboole_0('#skF_3') | ~r1_tarski(k1_relat_1(C_1229), '#skF_3') | v1_funct_2(C_1229, k1_relat_1(C_1229), B_1228) | ~v1_funct_1(C_1229) | ~v1_relat_1(C_1229))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_8617])).
% 11.04/4.52  tff(c_8645, plain, (![C_1232, B_1233]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'(k1_relat_1(C_1232), B_1233, C_1232))=k1_funct_1('#skF_5', '#skF_1'(k1_relat_1(C_1232), B_1233, C_1232)) | ~r1_tarski(k1_relat_1(C_1232), '#skF_3') | v1_funct_2(C_1232, k1_relat_1(C_1232), B_1233) | ~v1_funct_1(C_1232) | ~v1_relat_1(C_1232))), inference(negUnitSimplification, [status(thm)], [c_50, c_8643])).
% 11.04/4.52  tff(c_40, plain, (![E_41]: (r2_hidden(k3_funct_2('#skF_3', '#skF_4', '#skF_5', E_41), '#skF_2') | ~m1_subset_1(E_41, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 11.04/4.52  tff(c_8712, plain, (![C_1234, B_1235]: (r2_hidden(k1_funct_1('#skF_5', '#skF_1'(k1_relat_1(C_1234), B_1235, C_1234)), '#skF_2') | ~m1_subset_1('#skF_1'(k1_relat_1(C_1234), B_1235, C_1234), '#skF_3') | ~r1_tarski(k1_relat_1(C_1234), '#skF_3') | v1_funct_2(C_1234, k1_relat_1(C_1234), B_1235) | ~v1_funct_1(C_1234) | ~v1_relat_1(C_1234))), inference(superposition, [status(thm), theory('equality')], [c_8645, c_40])).
% 11.04/4.52  tff(c_30, plain, (![C_28, B_27]: (~r2_hidden(k1_funct_1(C_28, '#skF_1'(k1_relat_1(C_28), B_27, C_28)), B_27) | v1_funct_2(C_28, k1_relat_1(C_28), B_27) | ~v1_funct_1(C_28) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.04/4.52  tff(c_8720, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_8712, c_30])).
% 11.04/4.52  tff(c_8728, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_46, c_8720])).
% 11.04/4.52  tff(c_8730, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_8728])).
% 11.04/4.52  tff(c_8815, plain, (~v4_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_12, c_8730])).
% 11.04/4.52  tff(c_8819, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_91, c_8815])).
% 11.04/4.52  tff(c_8821, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_8728])).
% 11.04/4.52  tff(c_424, plain, (![C_150, B_151]: (r2_hidden('#skF_1'(k1_relat_1(C_150), B_151, C_150), k1_relat_1(C_150)) | m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_150), B_151))) | ~v1_funct_1(C_150) | ~v1_relat_1(C_150))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.04/4.52  tff(c_592, plain, (![C_182, B_183, B_184]: (m1_subset_1('#skF_1'(k1_relat_1(C_182), B_183, C_182), B_184) | ~r1_tarski(k1_relat_1(C_182), B_184) | m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_182), B_183))) | ~v1_funct_1(C_182) | ~v1_relat_1(C_182))), inference(resolution, [status(thm)], [c_424, c_138])).
% 11.04/4.52  tff(c_22, plain, (![A_19, B_20, C_21]: (k2_relset_1(A_19, B_20, C_21)=k2_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.04/4.52  tff(c_685, plain, (![C_182, B_183, B_184]: (k2_relset_1(k1_relat_1(C_182), B_183, C_182)=k2_relat_1(C_182) | m1_subset_1('#skF_1'(k1_relat_1(C_182), B_183, C_182), B_184) | ~r1_tarski(k1_relat_1(C_182), B_184) | ~v1_funct_1(C_182) | ~v1_relat_1(C_182))), inference(resolution, [status(thm)], [c_592, c_22])).
% 11.04/4.52  tff(c_8820, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_2')), inference(splitRight, [status(thm)], [c_8728])).
% 11.04/4.52  tff(c_8832, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_8820])).
% 11.04/4.52  tff(c_8845, plain, (k2_relset_1(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')=k2_relat_1('#skF_5') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_685, c_8832])).
% 11.04/4.52  tff(c_8868, plain, (k2_relset_1(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_46, c_8821, c_8845])).
% 11.04/4.52  tff(c_210, plain, (![A_92, B_93, C_94]: (m1_subset_1(k2_relset_1(A_92, B_93, C_94), k1_zfmisc_1(B_93)) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.04/4.52  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.04/4.52  tff(c_239, plain, (![A_92, B_93, C_94]: (r1_tarski(k2_relset_1(A_92, B_93, C_94), B_93) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(resolution, [status(thm)], [c_210, c_2])).
% 11.04/4.52  tff(c_684, plain, (![C_182, B_183, B_184]: (r1_tarski(k2_relset_1(k1_relat_1(C_182), B_183, C_182), B_183) | m1_subset_1('#skF_1'(k1_relat_1(C_182), B_183, C_182), B_184) | ~r1_tarski(k1_relat_1(C_182), B_184) | ~v1_funct_1(C_182) | ~v1_relat_1(C_182))), inference(resolution, [status(thm)], [c_592, c_239])).
% 11.04/4.52  tff(c_8938, plain, (![B_184]: (r1_tarski(k2_relat_1('#skF_5'), '#skF_2') | m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), B_184) | ~r1_tarski(k1_relat_1('#skF_5'), B_184) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8868, c_684])).
% 11.04/4.52  tff(c_8954, plain, (![B_184]: (r1_tarski(k2_relat_1('#skF_5'), '#skF_2') | m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), B_184) | ~r1_tarski(k1_relat_1('#skF_5'), B_184))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_46, c_8938])).
% 11.04/4.52  tff(c_8970, plain, (![B_1245]: (m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), B_1245) | ~r1_tarski(k1_relat_1('#skF_5'), B_1245))), inference(negUnitSimplification, [status(thm)], [c_155, c_8954])).
% 11.04/4.52  tff(c_8973, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_8970, c_8832])).
% 11.04/4.52  tff(c_9039, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8821, c_8973])).
% 11.04/4.52  tff(c_9041, plain, (m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_8820])).
% 11.04/4.52  tff(c_24, plain, (![A_22, B_23, C_24, D_25]: (k3_funct_2(A_22, B_23, C_24, D_25)=k1_funct_1(C_24, D_25) | ~m1_subset_1(D_25, A_22) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2(C_24, A_22, B_23) | ~v1_funct_1(C_24) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.04/4.52  tff(c_9085, plain, (![B_23, C_24]: (k3_funct_2('#skF_3', B_23, C_24, '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'))=k1_funct_1(C_24, '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_23))) | ~v1_funct_2(C_24, '#skF_3', B_23) | ~v1_funct_1(C_24) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_9041, c_24])).
% 11.04/4.52  tff(c_9176, plain, (![B_1256, C_1257]: (k3_funct_2('#skF_3', B_1256, C_1257, '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'))=k1_funct_1(C_1257, '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')) | ~m1_subset_1(C_1257, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_1256))) | ~v1_funct_2(C_1257, '#skF_3', B_1256) | ~v1_funct_1(C_1257))), inference(negUnitSimplification, [status(thm)], [c_50, c_9085])).
% 11.04/4.52  tff(c_9259, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_9176])).
% 11.04/4.52  tff(c_9282, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_9259])).
% 11.04/4.52  tff(c_9344, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9282, c_40])).
% 11.04/4.52  tff(c_9392, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9041, c_9344])).
% 11.04/4.52  tff(c_26, plain, (![C_28, B_27]: (~r2_hidden(k1_funct_1(C_28, '#skF_1'(k1_relat_1(C_28), B_27, C_28)), B_27) | m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_28), B_27))) | ~v1_funct_1(C_28) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_94])).
% 11.04/4.52  tff(c_9399, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_2'))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_9392, c_26])).
% 11.04/4.52  tff(c_9407, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_46, c_9399])).
% 11.04/4.52  tff(c_9459, plain, (r1_tarski('#skF_5', k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_2'))), inference(resolution, [status(thm)], [c_9407, c_2])).
% 11.04/4.52  tff(c_9452, plain, (k2_relset_1(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_9407, c_22])).
% 11.04/4.52  tff(c_279, plain, (![A_98, B_99, C_100]: (r1_tarski(k2_relset_1(A_98, B_99, C_100), B_99) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(resolution, [status(thm)], [c_210, c_2])).
% 11.04/4.52  tff(c_293, plain, (![A_98, B_99, A_1]: (r1_tarski(k2_relset_1(A_98, B_99, A_1), B_99) | ~r1_tarski(A_1, k2_zfmisc_1(A_98, B_99)))), inference(resolution, [status(thm)], [c_4, c_279])).
% 11.04/4.52  tff(c_9517, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_2') | ~r1_tarski('#skF_5', k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_9452, c_293])).
% 11.04/4.52  tff(c_9534, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9459, c_9517])).
% 11.04/4.52  tff(c_9536, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155, c_9534])).
% 11.04/4.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.04/4.52  
% 11.04/4.52  Inference rules
% 11.04/4.52  ----------------------
% 11.04/4.52  #Ref     : 0
% 11.04/4.52  #Sup     : 2228
% 11.04/4.52  #Fact    : 2
% 11.04/4.52  #Define  : 0
% 11.04/4.52  #Split   : 10
% 11.04/4.52  #Chain   : 0
% 11.04/4.52  #Close   : 0
% 11.04/4.52  
% 11.04/4.52  Ordering : KBO
% 11.04/4.52  
% 11.04/4.52  Simplification rules
% 11.04/4.52  ----------------------
% 11.04/4.52  #Subsume      : 158
% 11.04/4.52  #Demod        : 147
% 11.04/4.52  #Tautology    : 76
% 11.04/4.52  #SimpNegUnit  : 10
% 11.04/4.52  #BackRed      : 1
% 11.04/4.52  
% 11.04/4.52  #Partial instantiations: 0
% 11.04/4.52  #Strategies tried      : 1
% 11.04/4.52  
% 11.04/4.52  Timing (in seconds)
% 11.04/4.52  ----------------------
% 11.04/4.52  Preprocessing        : 0.32
% 11.04/4.52  Parsing              : 0.17
% 11.04/4.52  CNF conversion       : 0.02
% 11.04/4.52  Main loop            : 3.43
% 11.04/4.52  Inferencing          : 1.06
% 11.04/4.52  Reduction            : 0.75
% 11.04/4.52  Demodulation         : 0.51
% 11.04/4.52  BG Simplification    : 0.13
% 11.04/4.52  Subsumption          : 1.20
% 11.04/4.52  Abstraction          : 0.27
% 11.04/4.52  MUC search           : 0.00
% 11.04/4.52  Cooper               : 0.00
% 11.04/4.52  Total                : 3.79
% 11.04/4.52  Index Insertion      : 0.00
% 11.04/4.52  Index Deletion       : 0.00
% 11.04/4.52  Index Matching       : 0.00
% 11.04/4.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
