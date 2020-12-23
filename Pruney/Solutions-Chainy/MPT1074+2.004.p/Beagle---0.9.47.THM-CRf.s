%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:06 EST 2020

% Result     : Theorem 5.11s
% Output     : CNFRefutation 5.27s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 314 expanded)
%              Number of leaves         :   34 ( 124 expanded)
%              Depth                    :   22
%              Number of atoms          :  201 (1157 expanded)
%              Number of equality atoms :   15 (  54 expanded)
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

tff(f_113,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_funct_2)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_91,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_62,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_71,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_62])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_160,plain,(
    ! [A_74,B_75,C_76] :
      ( k2_relset_1(A_74,B_75,C_76) = k2_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_169,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_160])).

tff(c_38,plain,(
    ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_170,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_38])).

tff(c_177,plain,
    ( ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_170])).

tff(c_180,plain,(
    ~ v5_relat_1('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_177])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_111,plain,(
    ! [C_62,A_63,B_64] :
      ( v4_relat_1(C_62,A_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_120,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_111])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_44,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_32,plain,(
    ! [C_25,B_24] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_25),B_24,C_25),k1_relat_1(C_25))
      | v1_funct_2(C_25,k1_relat_1(C_25),B_24)
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_152,plain,(
    ! [A_70,C_71,B_72] :
      ( m1_subset_1(A_70,C_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(C_71))
      | ~ r2_hidden(A_70,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_182,plain,(
    ! [A_79,B_80,A_81] :
      ( m1_subset_1(A_79,B_80)
      | ~ r2_hidden(A_79,A_81)
      | ~ r1_tarski(A_81,B_80) ) ),
    inference(resolution,[status(thm)],[c_4,c_152])).

tff(c_187,plain,(
    ! [C_25,B_24,B_80] :
      ( m1_subset_1('#skF_1'(k1_relat_1(C_25),B_24,C_25),B_80)
      | ~ r1_tarski(k1_relat_1(C_25),B_80)
      | v1_funct_2(C_25,k1_relat_1(C_25),B_24)
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(resolution,[status(thm)],[c_32,c_182])).

tff(c_324,plain,(
    ! [A_130,B_131,C_132,D_133] :
      ( k3_funct_2(A_130,B_131,C_132,D_133) = k1_funct_1(C_132,D_133)
      | ~ m1_subset_1(D_133,A_130)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131)))
      | ~ v1_funct_2(C_132,A_130,B_131)
      | ~ v1_funct_1(C_132)
      | v1_xboole_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1381,plain,(
    ! [B_500,B_501,C_499,C_498,B_502] :
      ( k3_funct_2(B_502,B_500,C_499,'#skF_1'(k1_relat_1(C_498),B_501,C_498)) = k1_funct_1(C_499,'#skF_1'(k1_relat_1(C_498),B_501,C_498))
      | ~ m1_subset_1(C_499,k1_zfmisc_1(k2_zfmisc_1(B_502,B_500)))
      | ~ v1_funct_2(C_499,B_502,B_500)
      | ~ v1_funct_1(C_499)
      | v1_xboole_0(B_502)
      | ~ r1_tarski(k1_relat_1(C_498),B_502)
      | v1_funct_2(C_498,k1_relat_1(C_498),B_501)
      | ~ v1_funct_1(C_498)
      | ~ v1_relat_1(C_498) ) ),
    inference(resolution,[status(thm)],[c_187,c_324])).

tff(c_1423,plain,(
    ! [C_498,B_501] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'(k1_relat_1(C_498),B_501,C_498)) = k1_funct_1('#skF_5','#skF_1'(k1_relat_1(C_498),B_501,C_498))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_3')
      | ~ r1_tarski(k1_relat_1(C_498),'#skF_3')
      | v1_funct_2(C_498,k1_relat_1(C_498),B_501)
      | ~ v1_funct_1(C_498)
      | ~ v1_relat_1(C_498) ) ),
    inference(resolution,[status(thm)],[c_42,c_1381])).

tff(c_1440,plain,(
    ! [C_498,B_501] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'(k1_relat_1(C_498),B_501,C_498)) = k1_funct_1('#skF_5','#skF_1'(k1_relat_1(C_498),B_501,C_498))
      | v1_xboole_0('#skF_3')
      | ~ r1_tarski(k1_relat_1(C_498),'#skF_3')
      | v1_funct_2(C_498,k1_relat_1(C_498),B_501)
      | ~ v1_funct_1(C_498)
      | ~ v1_relat_1(C_498) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1423])).

tff(c_1442,plain,(
    ! [C_503,B_504] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'(k1_relat_1(C_503),B_504,C_503)) = k1_funct_1('#skF_5','#skF_1'(k1_relat_1(C_503),B_504,C_503))
      | ~ r1_tarski(k1_relat_1(C_503),'#skF_3')
      | v1_funct_2(C_503,k1_relat_1(C_503),B_504)
      | ~ v1_funct_1(C_503)
      | ~ v1_relat_1(C_503) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1440])).

tff(c_40,plain,(
    ! [E_38] :
      ( r2_hidden(k3_funct_2('#skF_3','#skF_4','#skF_5',E_38),'#skF_2')
      | ~ m1_subset_1(E_38,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1468,plain,(
    ! [C_505,B_506] :
      ( r2_hidden(k1_funct_1('#skF_5','#skF_1'(k1_relat_1(C_505),B_506,C_505)),'#skF_2')
      | ~ m1_subset_1('#skF_1'(k1_relat_1(C_505),B_506,C_505),'#skF_3')
      | ~ r1_tarski(k1_relat_1(C_505),'#skF_3')
      | v1_funct_2(C_505,k1_relat_1(C_505),B_506)
      | ~ v1_funct_1(C_505)
      | ~ v1_relat_1(C_505) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1442,c_40])).

tff(c_30,plain,(
    ! [C_25,B_24] :
      ( ~ r2_hidden(k1_funct_1(C_25,'#skF_1'(k1_relat_1(C_25),B_24,C_25)),B_24)
      | v1_funct_2(C_25,k1_relat_1(C_25),B_24)
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1476,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1468,c_30])).

tff(c_1484,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_46,c_1476])).

tff(c_1486,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1484])).

tff(c_1534,plain,
    ( ~ v4_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_1486])).

tff(c_1538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_120,c_1534])).

tff(c_1540,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1484])).

tff(c_267,plain,(
    ! [C_117,B_118] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_117),B_118,C_117),k1_relat_1(C_117))
      | m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_117),B_118)))
      | ~ v1_funct_1(C_117)
      | ~ v1_relat_1(C_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_157,plain,(
    ! [A_70,B_2,A_1] :
      ( m1_subset_1(A_70,B_2)
      | ~ r2_hidden(A_70,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_152])).

tff(c_340,plain,(
    ! [C_134,B_135,B_136] :
      ( m1_subset_1('#skF_1'(k1_relat_1(C_134),B_135,C_134),B_136)
      | ~ r1_tarski(k1_relat_1(C_134),B_136)
      | m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_134),B_135)))
      | ~ v1_funct_1(C_134)
      | ~ v1_relat_1(C_134) ) ),
    inference(resolution,[status(thm)],[c_267,c_157])).

tff(c_18,plain,(
    ! [C_15,B_14,A_13] :
      ( v5_relat_1(C_15,B_14)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_396,plain,(
    ! [C_134,B_135,B_136] :
      ( v5_relat_1(C_134,B_135)
      | m1_subset_1('#skF_1'(k1_relat_1(C_134),B_135,C_134),B_136)
      | ~ r1_tarski(k1_relat_1(C_134),B_136)
      | ~ v1_funct_1(C_134)
      | ~ v1_relat_1(C_134) ) ),
    inference(resolution,[status(thm)],[c_340,c_18])).

tff(c_1539,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3')
    | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1484])).

tff(c_1547,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1539])).

tff(c_1563,plain,
    ( v5_relat_1('#skF_5','#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_3')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_396,c_1547])).

tff(c_1582,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_46,c_1540,c_1563])).

tff(c_1584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_1582])).

tff(c_1586,plain,(
    m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1539])).

tff(c_24,plain,(
    ! [A_19,B_20,C_21,D_22] :
      ( k3_funct_2(A_19,B_20,C_21,D_22) = k1_funct_1(C_21,D_22)
      | ~ m1_subset_1(D_22,A_19)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ v1_funct_2(C_21,A_19,B_20)
      | ~ v1_funct_1(C_21)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1649,plain,(
    ! [B_20,C_21] :
      ( k3_funct_2('#skF_3',B_20,C_21,'#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')) = k1_funct_1(C_21,'#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'))
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_20)))
      | ~ v1_funct_2(C_21,'#skF_3',B_20)
      | ~ v1_funct_1(C_21)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1586,c_24])).

tff(c_1655,plain,(
    ! [B_515,C_516] :
      ( k3_funct_2('#skF_3',B_515,C_516,'#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')) = k1_funct_1(C_516,'#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'))
      | ~ m1_subset_1(C_516,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_515)))
      | ~ v1_funct_2(C_516,'#skF_3',B_515)
      | ~ v1_funct_1(C_516) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1649])).

tff(c_1706,plain,
    ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_1655])).

tff(c_1721,plain,(
    k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1706])).

tff(c_1778,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')),'#skF_2')
    | ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1721,c_40])).

tff(c_1798,plain,(
    r2_hidden(k1_funct_1('#skF_5','#skF_1'(k1_relat_1('#skF_5'),'#skF_2','#skF_5')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1586,c_1778])).

tff(c_26,plain,(
    ! [C_25,B_24] :
      ( ~ r2_hidden(k1_funct_1(C_25,'#skF_1'(k1_relat_1(C_25),B_24,C_25)),B_24)
      | m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_25),B_24)))
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1805,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1798,c_26])).

tff(c_1813,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_46,c_1805])).

tff(c_1836,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_1813,c_18])).

tff(c_1859,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_1836])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.11/1.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.27/1.99  
% 5.27/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.27/1.99  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 5.27/1.99  
% 5.27/1.99  %Foreground sorts:
% 5.27/1.99  
% 5.27/1.99  
% 5.27/1.99  %Background operators:
% 5.27/1.99  
% 5.27/1.99  
% 5.27/1.99  %Foreground operators:
% 5.27/1.99  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.27/1.99  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.27/1.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.27/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.27/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.27/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.27/1.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.27/1.99  tff('#skF_5', type, '#skF_5': $i).
% 5.27/1.99  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.27/1.99  tff('#skF_2', type, '#skF_2': $i).
% 5.27/1.99  tff('#skF_3', type, '#skF_3': $i).
% 5.27/1.99  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.27/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.27/1.99  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.27/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.27/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.27/1.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.27/1.99  tff('#skF_4', type, '#skF_4': $i).
% 5.27/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.27/1.99  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.27/1.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.27/1.99  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 5.27/1.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.27/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.27/1.99  
% 5.27/2.01  tff(f_113, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t191_funct_2)).
% 5.27/2.01  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.27/2.01  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 5.27/2.01  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.27/2.01  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.27/2.01  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 5.27/2.01  tff(f_91, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_funct_2)).
% 5.27/2.01  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.27/2.01  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 5.27/2.01  tff(f_74, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 5.27/2.01  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.27/2.01  tff(c_62, plain, (![C_44, A_45, B_46]: (v1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.27/2.01  tff(c_71, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_62])).
% 5.27/2.01  tff(c_14, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.27/2.01  tff(c_160, plain, (![A_74, B_75, C_76]: (k2_relset_1(A_74, B_75, C_76)=k2_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.27/2.01  tff(c_169, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_160])).
% 5.27/2.01  tff(c_38, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.27/2.01  tff(c_170, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_38])).
% 5.27/2.01  tff(c_177, plain, (~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_14, c_170])).
% 5.27/2.01  tff(c_180, plain, (~v5_relat_1('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_177])).
% 5.27/2.01  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.27/2.01  tff(c_111, plain, (![C_62, A_63, B_64]: (v4_relat_1(C_62, A_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.27/2.01  tff(c_120, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_111])).
% 5.27/2.01  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.27/2.01  tff(c_50, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.27/2.01  tff(c_44, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.27/2.01  tff(c_32, plain, (![C_25, B_24]: (r2_hidden('#skF_1'(k1_relat_1(C_25), B_24, C_25), k1_relat_1(C_25)) | v1_funct_2(C_25, k1_relat_1(C_25), B_24) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.27/2.01  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.27/2.01  tff(c_152, plain, (![A_70, C_71, B_72]: (m1_subset_1(A_70, C_71) | ~m1_subset_1(B_72, k1_zfmisc_1(C_71)) | ~r2_hidden(A_70, B_72))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.27/2.01  tff(c_182, plain, (![A_79, B_80, A_81]: (m1_subset_1(A_79, B_80) | ~r2_hidden(A_79, A_81) | ~r1_tarski(A_81, B_80))), inference(resolution, [status(thm)], [c_4, c_152])).
% 5.27/2.01  tff(c_187, plain, (![C_25, B_24, B_80]: (m1_subset_1('#skF_1'(k1_relat_1(C_25), B_24, C_25), B_80) | ~r1_tarski(k1_relat_1(C_25), B_80) | v1_funct_2(C_25, k1_relat_1(C_25), B_24) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(resolution, [status(thm)], [c_32, c_182])).
% 5.27/2.01  tff(c_324, plain, (![A_130, B_131, C_132, D_133]: (k3_funct_2(A_130, B_131, C_132, D_133)=k1_funct_1(C_132, D_133) | ~m1_subset_1(D_133, A_130) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))) | ~v1_funct_2(C_132, A_130, B_131) | ~v1_funct_1(C_132) | v1_xboole_0(A_130))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.27/2.01  tff(c_1381, plain, (![B_500, B_501, C_499, C_498, B_502]: (k3_funct_2(B_502, B_500, C_499, '#skF_1'(k1_relat_1(C_498), B_501, C_498))=k1_funct_1(C_499, '#skF_1'(k1_relat_1(C_498), B_501, C_498)) | ~m1_subset_1(C_499, k1_zfmisc_1(k2_zfmisc_1(B_502, B_500))) | ~v1_funct_2(C_499, B_502, B_500) | ~v1_funct_1(C_499) | v1_xboole_0(B_502) | ~r1_tarski(k1_relat_1(C_498), B_502) | v1_funct_2(C_498, k1_relat_1(C_498), B_501) | ~v1_funct_1(C_498) | ~v1_relat_1(C_498))), inference(resolution, [status(thm)], [c_187, c_324])).
% 5.27/2.01  tff(c_1423, plain, (![C_498, B_501]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'(k1_relat_1(C_498), B_501, C_498))=k1_funct_1('#skF_5', '#skF_1'(k1_relat_1(C_498), B_501, C_498)) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3') | ~r1_tarski(k1_relat_1(C_498), '#skF_3') | v1_funct_2(C_498, k1_relat_1(C_498), B_501) | ~v1_funct_1(C_498) | ~v1_relat_1(C_498))), inference(resolution, [status(thm)], [c_42, c_1381])).
% 5.27/2.01  tff(c_1440, plain, (![C_498, B_501]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'(k1_relat_1(C_498), B_501, C_498))=k1_funct_1('#skF_5', '#skF_1'(k1_relat_1(C_498), B_501, C_498)) | v1_xboole_0('#skF_3') | ~r1_tarski(k1_relat_1(C_498), '#skF_3') | v1_funct_2(C_498, k1_relat_1(C_498), B_501) | ~v1_funct_1(C_498) | ~v1_relat_1(C_498))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1423])).
% 5.27/2.01  tff(c_1442, plain, (![C_503, B_504]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'(k1_relat_1(C_503), B_504, C_503))=k1_funct_1('#skF_5', '#skF_1'(k1_relat_1(C_503), B_504, C_503)) | ~r1_tarski(k1_relat_1(C_503), '#skF_3') | v1_funct_2(C_503, k1_relat_1(C_503), B_504) | ~v1_funct_1(C_503) | ~v1_relat_1(C_503))), inference(negUnitSimplification, [status(thm)], [c_50, c_1440])).
% 5.27/2.01  tff(c_40, plain, (![E_38]: (r2_hidden(k3_funct_2('#skF_3', '#skF_4', '#skF_5', E_38), '#skF_2') | ~m1_subset_1(E_38, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.27/2.01  tff(c_1468, plain, (![C_505, B_506]: (r2_hidden(k1_funct_1('#skF_5', '#skF_1'(k1_relat_1(C_505), B_506, C_505)), '#skF_2') | ~m1_subset_1('#skF_1'(k1_relat_1(C_505), B_506, C_505), '#skF_3') | ~r1_tarski(k1_relat_1(C_505), '#skF_3') | v1_funct_2(C_505, k1_relat_1(C_505), B_506) | ~v1_funct_1(C_505) | ~v1_relat_1(C_505))), inference(superposition, [status(thm), theory('equality')], [c_1442, c_40])).
% 5.27/2.01  tff(c_30, plain, (![C_25, B_24]: (~r2_hidden(k1_funct_1(C_25, '#skF_1'(k1_relat_1(C_25), B_24, C_25)), B_24) | v1_funct_2(C_25, k1_relat_1(C_25), B_24) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.27/2.01  tff(c_1476, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1468, c_30])).
% 5.27/2.01  tff(c_1484, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_46, c_1476])).
% 5.27/2.01  tff(c_1486, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1484])).
% 5.27/2.01  tff(c_1534, plain, (~v4_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_1486])).
% 5.27/2.01  tff(c_1538, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_120, c_1534])).
% 5.27/2.01  tff(c_1540, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_1484])).
% 5.27/2.01  tff(c_267, plain, (![C_117, B_118]: (r2_hidden('#skF_1'(k1_relat_1(C_117), B_118, C_117), k1_relat_1(C_117)) | m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_117), B_118))) | ~v1_funct_1(C_117) | ~v1_relat_1(C_117))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.27/2.01  tff(c_157, plain, (![A_70, B_2, A_1]: (m1_subset_1(A_70, B_2) | ~r2_hidden(A_70, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_152])).
% 5.27/2.01  tff(c_340, plain, (![C_134, B_135, B_136]: (m1_subset_1('#skF_1'(k1_relat_1(C_134), B_135, C_134), B_136) | ~r1_tarski(k1_relat_1(C_134), B_136) | m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_134), B_135))) | ~v1_funct_1(C_134) | ~v1_relat_1(C_134))), inference(resolution, [status(thm)], [c_267, c_157])).
% 5.27/2.01  tff(c_18, plain, (![C_15, B_14, A_13]: (v5_relat_1(C_15, B_14) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.27/2.01  tff(c_396, plain, (![C_134, B_135, B_136]: (v5_relat_1(C_134, B_135) | m1_subset_1('#skF_1'(k1_relat_1(C_134), B_135, C_134), B_136) | ~r1_tarski(k1_relat_1(C_134), B_136) | ~v1_funct_1(C_134) | ~v1_relat_1(C_134))), inference(resolution, [status(thm)], [c_340, c_18])).
% 5.27/2.01  tff(c_1539, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), '#skF_2')), inference(splitRight, [status(thm)], [c_1484])).
% 5.27/2.01  tff(c_1547, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1539])).
% 5.27/2.01  tff(c_1563, plain, (v5_relat_1('#skF_5', '#skF_2') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_3') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_396, c_1547])).
% 5.27/2.01  tff(c_1582, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_46, c_1540, c_1563])).
% 5.27/2.01  tff(c_1584, plain, $false, inference(negUnitSimplification, [status(thm)], [c_180, c_1582])).
% 5.27/2.01  tff(c_1586, plain, (m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_1539])).
% 5.27/2.01  tff(c_24, plain, (![A_19, B_20, C_21, D_22]: (k3_funct_2(A_19, B_20, C_21, D_22)=k1_funct_1(C_21, D_22) | ~m1_subset_1(D_22, A_19) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~v1_funct_2(C_21, A_19, B_20) | ~v1_funct_1(C_21) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.27/2.01  tff(c_1649, plain, (![B_20, C_21]: (k3_funct_2('#skF_3', B_20, C_21, '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'))=k1_funct_1(C_21, '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_20))) | ~v1_funct_2(C_21, '#skF_3', B_20) | ~v1_funct_1(C_21) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_1586, c_24])).
% 5.27/2.01  tff(c_1655, plain, (![B_515, C_516]: (k3_funct_2('#skF_3', B_515, C_516, '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'))=k1_funct_1(C_516, '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')) | ~m1_subset_1(C_516, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_515))) | ~v1_funct_2(C_516, '#skF_3', B_515) | ~v1_funct_1(C_516))), inference(negUnitSimplification, [status(thm)], [c_50, c_1649])).
% 5.27/2.01  tff(c_1706, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_1655])).
% 5.27/2.01  tff(c_1721, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1706])).
% 5.27/2.01  tff(c_1778, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1721, c_40])).
% 5.27/2.01  tff(c_1798, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'(k1_relat_1('#skF_5'), '#skF_2', '#skF_5')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1586, c_1778])).
% 5.27/2.01  tff(c_26, plain, (![C_25, B_24]: (~r2_hidden(k1_funct_1(C_25, '#skF_1'(k1_relat_1(C_25), B_24, C_25)), B_24) | m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_25), B_24))) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.27/2.01  tff(c_1805, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_2'))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1798, c_26])).
% 5.27/2.01  tff(c_1813, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_46, c_1805])).
% 5.27/2.01  tff(c_1836, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_1813, c_18])).
% 5.27/2.01  tff(c_1859, plain, $false, inference(negUnitSimplification, [status(thm)], [c_180, c_1836])).
% 5.27/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.27/2.01  
% 5.27/2.01  Inference rules
% 5.27/2.01  ----------------------
% 5.27/2.01  #Ref     : 0
% 5.27/2.01  #Sup     : 379
% 5.27/2.01  #Fact    : 2
% 5.27/2.01  #Define  : 0
% 5.27/2.01  #Split   : 6
% 5.27/2.01  #Chain   : 0
% 5.27/2.01  #Close   : 0
% 5.27/2.01  
% 5.27/2.01  Ordering : KBO
% 5.27/2.01  
% 5.27/2.01  Simplification rules
% 5.27/2.01  ----------------------
% 5.27/2.01  #Subsume      : 56
% 5.27/2.01  #Demod        : 69
% 5.27/2.01  #Tautology    : 30
% 5.27/2.01  #SimpNegUnit  : 7
% 5.27/2.01  #BackRed      : 1
% 5.27/2.01  
% 5.27/2.01  #Partial instantiations: 0
% 5.27/2.01  #Strategies tried      : 1
% 5.27/2.01  
% 5.27/2.01  Timing (in seconds)
% 5.27/2.01  ----------------------
% 5.27/2.02  Preprocessing        : 0.31
% 5.27/2.02  Parsing              : 0.16
% 5.27/2.02  CNF conversion       : 0.02
% 5.27/2.02  Main loop            : 0.88
% 5.27/2.02  Inferencing          : 0.32
% 5.27/2.02  Reduction            : 0.21
% 5.27/2.02  Demodulation         : 0.13
% 5.27/2.02  BG Simplification    : 0.04
% 5.27/2.02  Subsumption          : 0.23
% 5.27/2.02  Abstraction          : 0.05
% 5.27/2.02  MUC search           : 0.00
% 5.27/2.02  Cooper               : 0.00
% 5.27/2.02  Total                : 1.23
% 5.27/2.02  Index Insertion      : 0.00
% 5.27/2.02  Index Deletion       : 0.00
% 5.27/2.02  Index Matching       : 0.00
% 5.27/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
