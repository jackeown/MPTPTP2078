%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0965+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:09 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   51 (  73 expanded)
%              Number of leaves         :   23 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   99 ( 187 expanded)
%              Number of equality atoms :   13 (  26 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_14,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_23,plain,(
    ! [A_16,B_17] :
      ( r2_hidden(A_16,B_17)
      | v1_xboole_0(B_17)
      | ~ m1_subset_1(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_12,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_27,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k1_funct_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_23,c_12])).

tff(c_28,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_27])).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10,plain,(
    ! [D_15,C_14,A_12,B_13] :
      ( r2_hidden(k1_funct_1(D_15,C_14),k2_relset_1(A_12,B_13,D_15))
      | k1_xboole_0 = B_13
      | ~ r2_hidden(C_14,A_12)
      | ~ m1_subset_1(D_15,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13)))
      | ~ v1_funct_2(D_15,A_12,B_13)
      | ~ v1_funct_1(D_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_39,plain,(
    ! [A_25,B_26,C_27] :
      ( m1_subset_1(k2_relset_1(A_25,B_26,C_27),k1_zfmisc_1(B_26))
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,(
    ! [A_6,C_8,B_7] :
      ( m1_subset_1(A_6,C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_55,plain,(
    ! [A_36,B_37,A_38,C_39] :
      ( m1_subset_1(A_36,B_37)
      | ~ r2_hidden(A_36,k2_relset_1(A_38,B_37,C_39))
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_38,B_37))) ) ),
    inference(resolution,[status(thm)],[c_39,c_6])).

tff(c_104,plain,(
    ! [D_54,C_55,B_56,A_57] :
      ( m1_subset_1(k1_funct_1(D_54,C_55),B_56)
      | k1_xboole_0 = B_56
      | ~ r2_hidden(C_55,A_57)
      | ~ m1_subset_1(D_54,k1_zfmisc_1(k2_zfmisc_1(A_57,B_56)))
      | ~ v1_funct_2(D_54,A_57,B_56)
      | ~ v1_funct_1(D_54) ) ),
    inference(resolution,[status(thm)],[c_10,c_55])).

tff(c_114,plain,(
    ! [D_58,B_59] :
      ( m1_subset_1(k1_funct_1(D_58,'#skF_3'),B_59)
      | k1_xboole_0 = B_59
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_59)))
      | ~ v1_funct_2(D_58,'#skF_1',B_59)
      | ~ v1_funct_1(D_58) ) ),
    inference(resolution,[status(thm)],[c_16,c_104])).

tff(c_121,plain,
    ( m1_subset_1(k1_funct_1('#skF_4','#skF_3'),'#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_114])).

tff(c_125,plain,
    ( m1_subset_1(k1_funct_1('#skF_4','#skF_3'),'#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_121])).

tff(c_127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_28,c_125])).

tff(c_128,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_27])).

tff(c_177,plain,(
    ! [D_87,C_88,A_89,B_90] :
      ( r2_hidden(k1_funct_1(D_87,C_88),k2_relset_1(A_89,B_90,D_87))
      | k1_xboole_0 = B_90
      | ~ r2_hidden(C_88,A_89)
      | ~ m1_subset_1(D_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ v1_funct_2(D_87,A_89,B_90)
      | ~ v1_funct_1(D_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_140,plain,(
    ! [A_67,B_68,C_69] :
      ( m1_subset_1(k2_relset_1(A_67,B_68,C_69),k1_zfmisc_1(B_68))
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_8,plain,(
    ! [C_11,B_10,A_9] :
      ( ~ v1_xboole_0(C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(C_11))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_146,plain,(
    ! [B_68,A_9,A_67,C_69] :
      ( ~ v1_xboole_0(B_68)
      | ~ r2_hidden(A_9,k2_relset_1(A_67,B_68,C_69))
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(resolution,[status(thm)],[c_140,c_8])).

tff(c_184,plain,(
    ! [B_91,C_92,A_93,D_94] :
      ( ~ v1_xboole_0(B_91)
      | k1_xboole_0 = B_91
      | ~ r2_hidden(C_92,A_93)
      | ~ m1_subset_1(D_94,k1_zfmisc_1(k2_zfmisc_1(A_93,B_91)))
      | ~ v1_funct_2(D_94,A_93,B_91)
      | ~ v1_funct_1(D_94) ) ),
    inference(resolution,[status(thm)],[c_177,c_146])).

tff(c_194,plain,(
    ! [B_95,D_96] :
      ( ~ v1_xboole_0(B_95)
      | k1_xboole_0 = B_95
      | ~ m1_subset_1(D_96,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_95)))
      | ~ v1_funct_2(D_96,'#skF_1',B_95)
      | ~ v1_funct_1(D_96) ) ),
    inference(resolution,[status(thm)],[c_16,c_184])).

tff(c_201,plain,
    ( ~ v1_xboole_0('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_194])).

tff(c_205,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_128,c_201])).

tff(c_207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_205])).

%------------------------------------------------------------------------------
