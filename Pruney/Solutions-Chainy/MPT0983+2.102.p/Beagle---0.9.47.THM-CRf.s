%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:15 EST 2020

% Result     : Theorem 5.91s
% Output     : CNFRefutation 6.11s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 329 expanded)
%              Number of leaves         :   47 ( 132 expanded)
%              Depth                    :   16
%              Number of atoms          :  247 ( 776 expanded)
%              Number of equality atoms :   39 (  99 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_176,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_117,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_70,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_115,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_95,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_156,axiom,(
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

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_134,axiom,(
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

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_60,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_89,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( v1_xboole_0(k2_zfmisc_1(A_10,B_11))
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_651,plain,(
    ! [C_134,B_135,A_136] :
      ( ~ v1_xboole_0(C_134)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(C_134))
      | ~ r2_hidden(A_136,B_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_667,plain,(
    ! [A_136] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_136,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70,c_651])).

tff(c_715,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_667])).

tff(c_720,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_715])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_68,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_66,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_52,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_30,plain,(
    ! [A_19] : v2_funct_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_76,plain,(
    ! [A_19] : v2_funct_1(k6_partfun1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_30])).

tff(c_48,plain,(
    ! [C_39,B_38,A_37,D_40,F_42,E_41] :
      ( m1_subset_1(k1_partfun1(A_37,B_38,C_39,D_40,E_41,F_42),k1_zfmisc_1(k2_zfmisc_1(A_37,D_40)))
      | ~ m1_subset_1(F_42,k1_zfmisc_1(k2_zfmisc_1(C_39,D_40)))
      | ~ v1_funct_1(F_42)
      | ~ m1_subset_1(E_41,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38)))
      | ~ v1_funct_1(E_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_42,plain,(
    ! [A_34] : m1_subset_1(k6_relat_1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_75,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_42])).

tff(c_62,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_1397,plain,(
    ! [D_194,C_195,A_196,B_197] :
      ( D_194 = C_195
      | ~ r2_relset_1(A_196,B_197,C_195,D_194)
      | ~ m1_subset_1(D_194,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197)))
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1407,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_62,c_1397])).

tff(c_1426,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_1407])).

tff(c_2107,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1426])).

tff(c_2547,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_2107])).

tff(c_2554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_68,c_64,c_2547])).

tff(c_2555,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1426])).

tff(c_58,plain,(
    ! [D_52,C_51,E_54,B_50,A_49] :
      ( k1_xboole_0 = C_51
      | v2_funct_1(D_52)
      | ~ v2_funct_1(k1_partfun1(A_49,B_50,B_50,C_51,D_52,E_54))
      | ~ m1_subset_1(E_54,k1_zfmisc_1(k2_zfmisc_1(B_50,C_51)))
      | ~ v1_funct_2(E_54,B_50,C_51)
      | ~ v1_funct_1(E_54)
      | ~ m1_subset_1(D_52,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | ~ v1_funct_2(D_52,A_49,B_50)
      | ~ v1_funct_1(D_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_2999,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2555,c_58])).

tff(c_3006,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_64,c_76,c_2999])).

tff(c_3007,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_3006])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3042,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3007,c_8])).

tff(c_3044,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_720,c_3042])).

tff(c_3047,plain,(
    ! [A_272] : ~ r2_hidden(A_272,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_667])).

tff(c_3054,plain,(
    ! [B_273] : r1_tarski('#skF_4',B_273) ),
    inference(resolution,[status(thm)],[c_6,c_3047])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_476,plain,(
    ! [C_119,A_120,B_121] :
      ( v1_xboole_0(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121)))
      | ~ v1_xboole_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_502,plain,(
    ! [A_122] :
      ( v1_xboole_0(k6_partfun1(A_122))
      | ~ v1_xboole_0(A_122) ) ),
    inference(resolution,[status(thm)],[c_75,c_476])).

tff(c_90,plain,(
    ! [B_59,A_60] :
      ( ~ v1_xboole_0(B_59)
      | B_59 = A_60
      | ~ v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_93,plain,(
    ! [A_60] :
      ( k1_xboole_0 = A_60
      | ~ v1_xboole_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_8,c_90])).

tff(c_520,plain,(
    ! [A_123] :
      ( k6_partfun1(A_123) = k1_xboole_0
      | ~ v1_xboole_0(A_123) ) ),
    inference(resolution,[status(thm)],[c_502,c_93])).

tff(c_532,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_520])).

tff(c_100,plain,(
    ! [A_62,B_63] :
      ( v1_xboole_0(k2_zfmisc_1(A_62,B_63))
      | ~ v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_109,plain,(
    ! [A_65,B_66] :
      ( k2_zfmisc_1(A_65,B_66) = k1_xboole_0
      | ~ v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_100,c_93])).

tff(c_116,plain,(
    ! [B_67] : k2_zfmisc_1(k1_xboole_0,B_67) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_109])).

tff(c_122,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_75])).

tff(c_133,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(A_70,B_71)
      | ~ m1_subset_1(A_70,k1_zfmisc_1(B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_150,plain,(
    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_122,c_133])).

tff(c_227,plain,(
    ! [B_84,A_85] :
      ( B_84 = A_85
      | ~ r1_tarski(B_84,A_85)
      | ~ r1_tarski(A_85,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_241,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_150,c_227])).

tff(c_250,plain,(
    ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_241])).

tff(c_537,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_250])).

tff(c_541,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_537])).

tff(c_542,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_241])).

tff(c_546,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_122])).

tff(c_653,plain,(
    ! [A_136] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_136,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_546,c_651])).

tff(c_669,plain,(
    ! [A_137] : ~ r2_hidden(A_137,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_653])).

tff(c_675,plain,(
    ! [B_138] : r1_tarski(k1_xboole_0,B_138) ),
    inference(resolution,[status(thm)],[c_6,c_669])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_686,plain,(
    ! [B_138] :
      ( k1_xboole_0 = B_138
      | ~ r1_tarski(B_138,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_675,c_10])).

tff(c_3069,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3054,c_686])).

tff(c_558,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_542,c_76])).

tff(c_3081,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3069,c_558])).

tff(c_3092,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_3081])).

tff(c_3093,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_3589,plain,(
    ! [C_345,A_346,B_347] :
      ( v1_relat_1(C_345)
      | ~ m1_subset_1(C_345,k1_zfmisc_1(k2_zfmisc_1(A_346,B_347))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3607,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_3589])).

tff(c_4192,plain,(
    ! [A_407,B_408,D_409] :
      ( r2_relset_1(A_407,B_408,D_409,D_409)
      | ~ m1_subset_1(D_409,k1_zfmisc_1(k2_zfmisc_1(A_407,B_408))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4209,plain,(
    ! [A_34] : r2_relset_1(A_34,A_34,k6_partfun1(A_34),k6_partfun1(A_34)) ),
    inference(resolution,[status(thm)],[c_75,c_4192])).

tff(c_4228,plain,(
    ! [A_411,B_412,C_413] :
      ( k2_relset_1(A_411,B_412,C_413) = k2_relat_1(C_413)
      | ~ m1_subset_1(C_413,k1_zfmisc_1(k2_zfmisc_1(A_411,B_412))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4253,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_4228])).

tff(c_4370,plain,(
    ! [D_415,C_416,A_417,B_418] :
      ( D_415 = C_416
      | ~ r2_relset_1(A_417,B_418,C_416,D_415)
      | ~ m1_subset_1(D_415,k1_zfmisc_1(k2_zfmisc_1(A_417,B_418)))
      | ~ m1_subset_1(C_416,k1_zfmisc_1(k2_zfmisc_1(A_417,B_418))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4380,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_62,c_4370])).

tff(c_4399,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_4380])).

tff(c_5008,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_4399])).

tff(c_5292,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_5008])).

tff(c_5299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_68,c_64,c_5292])).

tff(c_5300,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_4399])).

tff(c_6030,plain,(
    ! [A_506,B_507,C_508,D_509] :
      ( k2_relset_1(A_506,B_507,C_508) = B_507
      | ~ r2_relset_1(B_507,B_507,k1_partfun1(B_507,A_506,A_506,B_507,D_509,C_508),k6_partfun1(B_507))
      | ~ m1_subset_1(D_509,k1_zfmisc_1(k2_zfmisc_1(B_507,A_506)))
      | ~ v1_funct_2(D_509,B_507,A_506)
      | ~ v1_funct_1(D_509)
      | ~ m1_subset_1(C_508,k1_zfmisc_1(k2_zfmisc_1(A_506,B_507)))
      | ~ v1_funct_2(C_508,A_506,B_507)
      | ~ v1_funct_1(C_508) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_6039,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5300,c_6030])).

tff(c_6053,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_74,c_72,c_70,c_4209,c_4253,c_6039])).

tff(c_3609,plain,(
    ! [B_348,A_349] :
      ( v5_relat_1(B_348,A_349)
      | ~ r1_tarski(k2_relat_1(B_348),A_349)
      | ~ v1_relat_1(B_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3614,plain,(
    ! [B_348] :
      ( v5_relat_1(B_348,k2_relat_1(B_348))
      | ~ v1_relat_1(B_348) ) ),
    inference(resolution,[status(thm)],[c_14,c_3609])).

tff(c_3952,plain,(
    ! [B_392] :
      ( v2_funct_2(B_392,k2_relat_1(B_392))
      | ~ v5_relat_1(B_392,k2_relat_1(B_392))
      | ~ v1_relat_1(B_392) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3956,plain,(
    ! [B_348] :
      ( v2_funct_2(B_348,k2_relat_1(B_348))
      | ~ v1_relat_1(B_348) ) ),
    inference(resolution,[status(thm)],[c_3614,c_3952])).

tff(c_6067,plain,
    ( v2_funct_2('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6053,c_3956])).

tff(c_6087,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3607,c_6067])).

tff(c_6089,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3093,c_6087])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.91/2.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.00/2.11  
% 6.00/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.00/2.12  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.00/2.12  
% 6.00/2.12  %Foreground sorts:
% 6.00/2.12  
% 6.00/2.12  
% 6.00/2.12  %Background operators:
% 6.00/2.12  
% 6.00/2.12  
% 6.00/2.12  %Foreground operators:
% 6.00/2.12  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.00/2.12  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.00/2.12  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.00/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.00/2.12  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.00/2.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.00/2.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.00/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.00/2.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.00/2.12  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.00/2.12  tff('#skF_5', type, '#skF_5': $i).
% 6.00/2.12  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.00/2.12  tff('#skF_2', type, '#skF_2': $i).
% 6.00/2.12  tff('#skF_3', type, '#skF_3': $i).
% 6.00/2.12  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.00/2.12  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.00/2.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.00/2.12  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.00/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.00/2.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.00/2.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.00/2.12  tff('#skF_4', type, '#skF_4': $i).
% 6.00/2.12  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.00/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.00/2.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.00/2.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.00/2.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.00/2.12  
% 6.11/2.14  tff(f_176, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 6.11/2.14  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.11/2.14  tff(f_51, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 6.11/2.14  tff(f_62, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 6.11/2.14  tff(f_117, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.11/2.14  tff(f_70, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 6.11/2.14  tff(f_115, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.11/2.14  tff(f_95, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 6.11/2.14  tff(f_93, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.11/2.14  tff(f_156, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 6.11/2.14  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.11/2.14  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.11/2.14  tff(f_81, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 6.11/2.14  tff(f_47, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 6.11/2.14  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.11/2.14  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.11/2.14  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.11/2.14  tff(f_134, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 6.11/2.14  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 6.11/2.14  tff(f_103, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 6.11/2.14  tff(c_60, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_176])).
% 6.11/2.14  tff(c_89, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_60])).
% 6.11/2.14  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.11/2.14  tff(c_18, plain, (![A_10, B_11]: (v1_xboole_0(k2_zfmisc_1(A_10, B_11)) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.11/2.14  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_176])).
% 6.11/2.14  tff(c_651, plain, (![C_134, B_135, A_136]: (~v1_xboole_0(C_134) | ~m1_subset_1(B_135, k1_zfmisc_1(C_134)) | ~r2_hidden(A_136, B_135))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.11/2.14  tff(c_667, plain, (![A_136]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_136, '#skF_4'))), inference(resolution, [status(thm)], [c_70, c_651])).
% 6.11/2.14  tff(c_715, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_667])).
% 6.11/2.14  tff(c_720, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_715])).
% 6.11/2.14  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_176])).
% 6.11/2.14  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_176])).
% 6.11/2.14  tff(c_68, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_176])).
% 6.11/2.14  tff(c_66, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 6.11/2.14  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_176])).
% 6.11/2.14  tff(c_52, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.11/2.14  tff(c_30, plain, (![A_19]: (v2_funct_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.11/2.14  tff(c_76, plain, (![A_19]: (v2_funct_1(k6_partfun1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_30])).
% 6.11/2.14  tff(c_48, plain, (![C_39, B_38, A_37, D_40, F_42, E_41]: (m1_subset_1(k1_partfun1(A_37, B_38, C_39, D_40, E_41, F_42), k1_zfmisc_1(k2_zfmisc_1(A_37, D_40))) | ~m1_subset_1(F_42, k1_zfmisc_1(k2_zfmisc_1(C_39, D_40))) | ~v1_funct_1(F_42) | ~m1_subset_1(E_41, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))) | ~v1_funct_1(E_41))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.11/2.14  tff(c_42, plain, (![A_34]: (m1_subset_1(k6_relat_1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.11/2.14  tff(c_75, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_42])).
% 6.11/2.14  tff(c_62, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_176])).
% 6.11/2.14  tff(c_1397, plain, (![D_194, C_195, A_196, B_197]: (D_194=C_195 | ~r2_relset_1(A_196, B_197, C_195, D_194) | ~m1_subset_1(D_194, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.11/2.14  tff(c_1407, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_62, c_1397])).
% 6.11/2.14  tff(c_1426, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_1407])).
% 6.11/2.14  tff(c_2107, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1426])).
% 6.11/2.14  tff(c_2547, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_2107])).
% 6.11/2.14  tff(c_2554, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_68, c_64, c_2547])).
% 6.11/2.14  tff(c_2555, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1426])).
% 6.11/2.14  tff(c_58, plain, (![D_52, C_51, E_54, B_50, A_49]: (k1_xboole_0=C_51 | v2_funct_1(D_52) | ~v2_funct_1(k1_partfun1(A_49, B_50, B_50, C_51, D_52, E_54)) | ~m1_subset_1(E_54, k1_zfmisc_1(k2_zfmisc_1(B_50, C_51))) | ~v1_funct_2(E_54, B_50, C_51) | ~v1_funct_1(E_54) | ~m1_subset_1(D_52, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | ~v1_funct_2(D_52, A_49, B_50) | ~v1_funct_1(D_52))), inference(cnfTransformation, [status(thm)], [f_156])).
% 6.11/2.14  tff(c_2999, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2555, c_58])).
% 6.11/2.14  tff(c_3006, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_66, c_64, c_76, c_2999])).
% 6.11/2.14  tff(c_3007, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_89, c_3006])).
% 6.11/2.14  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.11/2.14  tff(c_3042, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3007, c_8])).
% 6.11/2.14  tff(c_3044, plain, $false, inference(negUnitSimplification, [status(thm)], [c_720, c_3042])).
% 6.11/2.14  tff(c_3047, plain, (![A_272]: (~r2_hidden(A_272, '#skF_4'))), inference(splitRight, [status(thm)], [c_667])).
% 6.11/2.14  tff(c_3054, plain, (![B_273]: (r1_tarski('#skF_4', B_273))), inference(resolution, [status(thm)], [c_6, c_3047])).
% 6.11/2.14  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.11/2.14  tff(c_476, plain, (![C_119, A_120, B_121]: (v1_xboole_0(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))) | ~v1_xboole_0(A_120))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.11/2.14  tff(c_502, plain, (![A_122]: (v1_xboole_0(k6_partfun1(A_122)) | ~v1_xboole_0(A_122))), inference(resolution, [status(thm)], [c_75, c_476])).
% 6.11/2.14  tff(c_90, plain, (![B_59, A_60]: (~v1_xboole_0(B_59) | B_59=A_60 | ~v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.11/2.14  tff(c_93, plain, (![A_60]: (k1_xboole_0=A_60 | ~v1_xboole_0(A_60))), inference(resolution, [status(thm)], [c_8, c_90])).
% 6.11/2.14  tff(c_520, plain, (![A_123]: (k6_partfun1(A_123)=k1_xboole_0 | ~v1_xboole_0(A_123))), inference(resolution, [status(thm)], [c_502, c_93])).
% 6.11/2.14  tff(c_532, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_520])).
% 6.11/2.14  tff(c_100, plain, (![A_62, B_63]: (v1_xboole_0(k2_zfmisc_1(A_62, B_63)) | ~v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.11/2.14  tff(c_109, plain, (![A_65, B_66]: (k2_zfmisc_1(A_65, B_66)=k1_xboole_0 | ~v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_100, c_93])).
% 6.11/2.14  tff(c_116, plain, (![B_67]: (k2_zfmisc_1(k1_xboole_0, B_67)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_109])).
% 6.11/2.14  tff(c_122, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_116, c_75])).
% 6.11/2.14  tff(c_133, plain, (![A_70, B_71]: (r1_tarski(A_70, B_71) | ~m1_subset_1(A_70, k1_zfmisc_1(B_71)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.11/2.14  tff(c_150, plain, (r1_tarski(k6_partfun1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_122, c_133])).
% 6.11/2.14  tff(c_227, plain, (![B_84, A_85]: (B_84=A_85 | ~r1_tarski(B_84, A_85) | ~r1_tarski(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.11/2.14  tff(c_241, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_150, c_227])).
% 6.11/2.14  tff(c_250, plain, (~r1_tarski(k1_xboole_0, k6_partfun1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_241])).
% 6.11/2.14  tff(c_537, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_532, c_250])).
% 6.11/2.14  tff(c_541, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_537])).
% 6.11/2.14  tff(c_542, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_241])).
% 6.11/2.14  tff(c_546, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_542, c_122])).
% 6.11/2.14  tff(c_653, plain, (![A_136]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_136, k1_xboole_0))), inference(resolution, [status(thm)], [c_546, c_651])).
% 6.11/2.14  tff(c_669, plain, (![A_137]: (~r2_hidden(A_137, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_653])).
% 6.11/2.14  tff(c_675, plain, (![B_138]: (r1_tarski(k1_xboole_0, B_138))), inference(resolution, [status(thm)], [c_6, c_669])).
% 6.11/2.14  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.11/2.14  tff(c_686, plain, (![B_138]: (k1_xboole_0=B_138 | ~r1_tarski(B_138, k1_xboole_0))), inference(resolution, [status(thm)], [c_675, c_10])).
% 6.11/2.14  tff(c_3069, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_3054, c_686])).
% 6.11/2.14  tff(c_558, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_542, c_76])).
% 6.11/2.14  tff(c_3081, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3069, c_558])).
% 6.11/2.14  tff(c_3092, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_3081])).
% 6.11/2.14  tff(c_3093, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_60])).
% 6.11/2.14  tff(c_3589, plain, (![C_345, A_346, B_347]: (v1_relat_1(C_345) | ~m1_subset_1(C_345, k1_zfmisc_1(k2_zfmisc_1(A_346, B_347))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.11/2.14  tff(c_3607, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_3589])).
% 6.11/2.14  tff(c_4192, plain, (![A_407, B_408, D_409]: (r2_relset_1(A_407, B_408, D_409, D_409) | ~m1_subset_1(D_409, k1_zfmisc_1(k2_zfmisc_1(A_407, B_408))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.11/2.14  tff(c_4209, plain, (![A_34]: (r2_relset_1(A_34, A_34, k6_partfun1(A_34), k6_partfun1(A_34)))), inference(resolution, [status(thm)], [c_75, c_4192])).
% 6.11/2.14  tff(c_4228, plain, (![A_411, B_412, C_413]: (k2_relset_1(A_411, B_412, C_413)=k2_relat_1(C_413) | ~m1_subset_1(C_413, k1_zfmisc_1(k2_zfmisc_1(A_411, B_412))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.11/2.14  tff(c_4253, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_4228])).
% 6.11/2.14  tff(c_4370, plain, (![D_415, C_416, A_417, B_418]: (D_415=C_416 | ~r2_relset_1(A_417, B_418, C_416, D_415) | ~m1_subset_1(D_415, k1_zfmisc_1(k2_zfmisc_1(A_417, B_418))) | ~m1_subset_1(C_416, k1_zfmisc_1(k2_zfmisc_1(A_417, B_418))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.11/2.14  tff(c_4380, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_62, c_4370])).
% 6.11/2.14  tff(c_4399, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_4380])).
% 6.11/2.14  tff(c_5008, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_4399])).
% 6.11/2.14  tff(c_5292, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_5008])).
% 6.11/2.14  tff(c_5299, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_68, c_64, c_5292])).
% 6.11/2.14  tff(c_5300, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_4399])).
% 6.11/2.14  tff(c_6030, plain, (![A_506, B_507, C_508, D_509]: (k2_relset_1(A_506, B_507, C_508)=B_507 | ~r2_relset_1(B_507, B_507, k1_partfun1(B_507, A_506, A_506, B_507, D_509, C_508), k6_partfun1(B_507)) | ~m1_subset_1(D_509, k1_zfmisc_1(k2_zfmisc_1(B_507, A_506))) | ~v1_funct_2(D_509, B_507, A_506) | ~v1_funct_1(D_509) | ~m1_subset_1(C_508, k1_zfmisc_1(k2_zfmisc_1(A_506, B_507))) | ~v1_funct_2(C_508, A_506, B_507) | ~v1_funct_1(C_508))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.11/2.14  tff(c_6039, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5300, c_6030])).
% 6.11/2.14  tff(c_6053, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_74, c_72, c_70, c_4209, c_4253, c_6039])).
% 6.11/2.14  tff(c_3609, plain, (![B_348, A_349]: (v5_relat_1(B_348, A_349) | ~r1_tarski(k2_relat_1(B_348), A_349) | ~v1_relat_1(B_348))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.11/2.14  tff(c_3614, plain, (![B_348]: (v5_relat_1(B_348, k2_relat_1(B_348)) | ~v1_relat_1(B_348))), inference(resolution, [status(thm)], [c_14, c_3609])).
% 6.11/2.14  tff(c_3952, plain, (![B_392]: (v2_funct_2(B_392, k2_relat_1(B_392)) | ~v5_relat_1(B_392, k2_relat_1(B_392)) | ~v1_relat_1(B_392))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.11/2.14  tff(c_3956, plain, (![B_348]: (v2_funct_2(B_348, k2_relat_1(B_348)) | ~v1_relat_1(B_348))), inference(resolution, [status(thm)], [c_3614, c_3952])).
% 6.11/2.14  tff(c_6067, plain, (v2_funct_2('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6053, c_3956])).
% 6.11/2.14  tff(c_6087, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3607, c_6067])).
% 6.11/2.14  tff(c_6089, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3093, c_6087])).
% 6.11/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.11/2.14  
% 6.11/2.14  Inference rules
% 6.11/2.14  ----------------------
% 6.11/2.14  #Ref     : 0
% 6.11/2.14  #Sup     : 1434
% 6.11/2.14  #Fact    : 0
% 6.11/2.14  #Define  : 0
% 6.11/2.14  #Split   : 21
% 6.11/2.14  #Chain   : 0
% 6.11/2.14  #Close   : 0
% 6.11/2.14  
% 6.11/2.14  Ordering : KBO
% 6.11/2.14  
% 6.11/2.14  Simplification rules
% 6.11/2.14  ----------------------
% 6.11/2.14  #Subsume      : 264
% 6.11/2.14  #Demod        : 1170
% 6.11/2.14  #Tautology    : 671
% 6.11/2.14  #SimpNegUnit  : 5
% 6.11/2.14  #BackRed      : 62
% 6.11/2.14  
% 6.11/2.14  #Partial instantiations: 0
% 6.11/2.14  #Strategies tried      : 1
% 6.11/2.14  
% 6.11/2.14  Timing (in seconds)
% 6.11/2.14  ----------------------
% 6.11/2.14  Preprocessing        : 0.35
% 6.11/2.14  Parsing              : 0.19
% 6.11/2.14  CNF conversion       : 0.02
% 6.11/2.14  Main loop            : 1.01
% 6.11/2.14  Inferencing          : 0.32
% 6.11/2.14  Reduction            : 0.35
% 6.11/2.14  Demodulation         : 0.25
% 6.11/2.14  BG Simplification    : 0.04
% 6.11/2.14  Subsumption          : 0.22
% 6.11/2.14  Abstraction          : 0.05
% 6.11/2.14  MUC search           : 0.00
% 6.11/2.14  Cooper               : 0.00
% 6.11/2.14  Total                : 1.40
% 6.11/2.14  Index Insertion      : 0.00
% 6.11/2.14  Index Deletion       : 0.00
% 6.11/2.14  Index Matching       : 0.00
% 6.11/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
