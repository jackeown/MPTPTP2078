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
% DateTime   : Thu Dec  3 10:08:19 EST 2020

% Result     : Theorem 4.06s
% Output     : CNFRefutation 4.06s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 388 expanded)
%              Number of leaves         :   41 ( 145 expanded)
%              Depth                    :   14
%              Number of atoms          :  188 ( 808 expanded)
%              Number of equality atoms :   30 ( 115 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_149,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_128,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_91,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_108,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_114,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_34,plain,(
    ! [A_27,B_28] : v1_relat_1(k2_zfmisc_1(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1552,plain,(
    ! [B_220,A_221] :
      ( v1_relat_1(B_220)
      | ~ m1_subset_1(B_220,k1_zfmisc_1(A_221))
      | ~ v1_relat_1(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1555,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_1552])).

tff(c_1558,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1555])).

tff(c_211,plain,(
    ! [B_84,A_85] :
      ( v1_relat_1(B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_85))
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_214,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_211])).

tff(c_217,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_214])).

tff(c_692,plain,(
    ! [C_137,B_138,A_139] :
      ( v5_relat_1(C_137,B_138)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_706,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_692])).

tff(c_30,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k2_relat_1(B_25),A_24)
      | ~ v5_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_897,plain,(
    ! [A_151,B_152,C_153] :
      ( k2_relset_1(A_151,B_152,C_153) = k2_relat_1(C_153)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_916,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_897])).

tff(c_218,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_1'(A_86,B_87),B_87)
      | r1_xboole_0(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,B_20)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_417,plain,(
    ! [A_107,B_108] :
      ( m1_subset_1('#skF_1'(A_107,B_108),B_108)
      | r1_xboole_0(A_107,B_108) ) ),
    inference(resolution,[status(thm)],[c_218,c_24])).

tff(c_171,plain,(
    ! [A_77,B_78] :
      ( r2_hidden('#skF_1'(A_77,B_78),A_77)
      | r1_xboole_0(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_46,plain,(
    ! [D_50] :
      ( ~ r2_hidden(D_50,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_50,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_187,plain,(
    ! [B_78] :
      ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5'),B_78),'#skF_4')
      | r1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5'),B_78) ) ),
    inference(resolution,[status(thm)],[c_171,c_46])).

tff(c_427,plain,(
    r1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_417,c_187])).

tff(c_32,plain,(
    ! [A_26] :
      ( v1_xboole_0(k1_relat_1(A_26))
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_82,plain,(
    ! [A_58,B_59] :
      ( v1_xboole_0(k2_zfmisc_1(A_58,B_59))
      | ~ v1_xboole_0(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    ! [A_62,B_63] :
      ( k2_zfmisc_1(A_62,B_63) = k1_xboole_0
      | ~ v1_xboole_0(B_63) ) ),
    inference(resolution,[status(thm)],[c_82,c_4])).

tff(c_142,plain,(
    ! [A_74,A_75] :
      ( k2_zfmisc_1(A_74,k1_relat_1(A_75)) = k1_xboole_0
      | ~ v1_xboole_0(A_75) ) ),
    inference(resolution,[status(thm)],[c_32,c_92])).

tff(c_153,plain,(
    ! [A_75] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_xboole_0(A_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_34])).

tff(c_165,plain,(
    ! [A_75] : ~ v1_xboole_0(A_75) ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( ~ r1_xboole_0(B_16,A_15)
      | ~ r1_tarski(B_16,A_15)
      | v1_xboole_0(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_203,plain,(
    ! [B_16,A_15] :
      ( ~ r1_xboole_0(B_16,A_15)
      | ~ r1_tarski(B_16,A_15) ) ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_20])).

tff(c_451,plain,(
    ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_427,c_203])).

tff(c_924,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_916,c_451])).

tff(c_973,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_924])).

tff(c_977,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_706,c_973])).

tff(c_978,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_1471,plain,(
    ! [A_216] :
      ( r1_tarski(A_216,k2_zfmisc_1(k1_relat_1(A_216),k2_relat_1(A_216)))
      | ~ v1_relat_1(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1046,plain,(
    ! [A_166,B_167] :
      ( r2_hidden('#skF_1'(A_166,B_167),A_166)
      | r1_xboole_0(A_166,B_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_117,plain,(
    ! [A_65,B_66,C_67] :
      ( ~ r1_xboole_0(A_65,B_66)
      | ~ r2_hidden(C_67,k3_xboole_0(A_65,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_121,plain,(
    ! [A_68,C_69] :
      ( ~ r1_xboole_0(A_68,A_68)
      | ~ r2_hidden(C_69,A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_117])).

tff(c_124,plain,(
    ! [C_69] : ~ r2_hidden(C_69,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_121])).

tff(c_1067,plain,(
    ! [B_170] : r1_xboole_0(k1_xboole_0,B_170) ),
    inference(resolution,[status(thm)],[c_1046,c_124])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( v1_xboole_0(k2_zfmisc_1(A_17,B_18))
      | ~ v1_xboole_0(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_151,plain,(
    ! [A_75] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k1_relat_1(A_75))
      | ~ v1_xboole_0(A_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_22])).

tff(c_980,plain,(
    ! [A_155] :
      ( ~ v1_xboole_0(k1_relat_1(A_155))
      | ~ v1_xboole_0(A_155) ) ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_990,plain,(
    ! [A_26] : ~ v1_xboole_0(A_26) ),
    inference(resolution,[status(thm)],[c_32,c_980])).

tff(c_994,plain,(
    ! [B_16,A_15] :
      ( ~ r1_xboole_0(B_16,A_15)
      | ~ r1_tarski(B_16,A_15) ) ),
    inference(negUnitSimplification,[status(thm)],[c_990,c_20])).

tff(c_1078,plain,(
    ! [B_170] : ~ r1_tarski(k1_xboole_0,B_170) ),
    inference(resolution,[status(thm)],[c_1067,c_994])).

tff(c_1483,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1471,c_1078])).

tff(c_1494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_978,c_1483])).

tff(c_1495,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_90,plain,(
    ! [A_58,B_59] :
      ( k2_zfmisc_1(A_58,B_59) = k1_xboole_0
      | ~ v1_xboole_0(B_59) ) ),
    inference(resolution,[status(thm)],[c_82,c_4])).

tff(c_1509,plain,(
    ! [A_58] : k2_zfmisc_1(A_58,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1495,c_90])).

tff(c_1676,plain,(
    ! [C_237,B_238,A_239] :
      ( v5_relat_1(C_237,B_238)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_239,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1696,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1676])).

tff(c_2425,plain,(
    ! [A_292,B_293,C_294] :
      ( k2_relset_1(A_292,B_293,C_294) = k2_relat_1(C_294)
      | ~ m1_subset_1(C_294,k1_zfmisc_1(k2_zfmisc_1(A_292,B_293))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2453,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_2425])).

tff(c_1562,plain,(
    ! [A_222,B_223] :
      ( r2_hidden('#skF_1'(A_222,B_223),B_223)
      | r1_xboole_0(A_222,B_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1581,plain,(
    ! [A_222,B_223] :
      ( m1_subset_1('#skF_1'(A_222,B_223),B_223)
      | r1_xboole_0(A_222,B_223) ) ),
    inference(resolution,[status(thm)],[c_1562,c_24])).

tff(c_1582,plain,(
    ! [A_224,B_225] :
      ( r2_hidden('#skF_1'(A_224,B_225),A_224)
      | r1_xboole_0(A_224,B_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1729,plain,(
    ! [B_244] :
      ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5'),B_244),'#skF_4')
      | r1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5'),B_244) ) ),
    inference(resolution,[status(thm)],[c_1582,c_46])).

tff(c_1734,plain,(
    r1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1581,c_1729])).

tff(c_1804,plain,
    ( ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1734,c_20])).

tff(c_1909,plain,(
    ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1804])).

tff(c_2456,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2453,c_1909])).

tff(c_2495,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_2456])).

tff(c_2499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1558,c_1696,c_2495])).

tff(c_2500,plain,(
    v1_xboole_0(k2_relset_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1804])).

tff(c_2512,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2500,c_4])).

tff(c_2812,plain,(
    ! [A_320,B_321,C_322] :
      ( k2_relset_1(A_320,B_321,C_322) = k2_relat_1(C_322)
      | ~ m1_subset_1(C_322,k1_zfmisc_1(k2_zfmisc_1(A_320,B_321))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2836,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_2812])).

tff(c_2841,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2512,c_2836])).

tff(c_36,plain,(
    ! [A_29] :
      ( r1_tarski(A_29,k2_zfmisc_1(k1_relat_1(A_29),k2_relat_1(A_29)))
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2848,plain,
    ( r1_tarski('#skF_5',k2_zfmisc_1(k1_relat_1('#skF_5'),k1_xboole_0))
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2841,c_36])).

tff(c_2860,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1558,c_1509,c_2848])).

tff(c_1603,plain,(
    ! [A_226] : r1_xboole_0(A_226,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1562,c_124])).

tff(c_1614,plain,(
    ! [A_226] :
      ( ~ r1_tarski(A_226,k1_xboole_0)
      | v1_xboole_0(A_226) ) ),
    inference(resolution,[status(thm)],[c_1603,c_20])).

tff(c_2869,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2860,c_1614])).

tff(c_2880,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2869,c_4])).

tff(c_48,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2910,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2880,c_48])).

tff(c_66,plain,(
    ! [A_55] :
      ( v1_xboole_0(k1_relat_1(A_55))
      | ~ v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_70,plain,(
    ! [A_55] :
      ( k1_relat_1(A_55) = k1_xboole_0
      | ~ v1_xboole_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_66,c_4])).

tff(c_2879,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2869,c_70])).

tff(c_2919,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2880,c_2879])).

tff(c_2934,plain,(
    ! [A_323,B_324,C_325] :
      ( k1_relset_1(A_323,B_324,C_325) = k1_relat_1(C_325)
      | ~ m1_subset_1(C_325,k1_zfmisc_1(k2_zfmisc_1(A_323,B_324))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2949,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_2934])).

tff(c_2954,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2919,c_2949])).

tff(c_3043,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2910,c_2954])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.06/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.06/1.73  
% 4.06/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.06/1.73  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.06/1.73  
% 4.06/1.73  %Foreground sorts:
% 4.06/1.73  
% 4.06/1.73  
% 4.06/1.73  %Background operators:
% 4.06/1.73  
% 4.06/1.73  
% 4.06/1.73  %Foreground operators:
% 4.06/1.73  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.06/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.06/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.06/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.06/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.06/1.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.06/1.73  tff('#skF_5', type, '#skF_5': $i).
% 4.06/1.73  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.06/1.73  tff('#skF_3', type, '#skF_3': $i).
% 4.06/1.73  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.06/1.73  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.06/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.06/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.06/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.06/1.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.06/1.73  tff('#skF_4', type, '#skF_4': $i).
% 4.06/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.06/1.73  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.06/1.73  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.06/1.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.06/1.73  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.06/1.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.06/1.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.06/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.06/1.73  
% 4.06/1.75  tff(f_110, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.06/1.75  tff(f_149, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 4.06/1.75  tff(f_98, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.06/1.75  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.06/1.75  tff(f_104, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.06/1.75  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.06/1.75  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.06/1.75  tff(f_91, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 4.06/1.75  tff(f_108, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 4.06/1.75  tff(f_87, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 4.06/1.75  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.06/1.75  tff(f_83, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 4.06/1.75  tff(f_114, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 4.06/1.75  tff(f_75, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 4.06/1.75  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.06/1.75  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.06/1.75  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.06/1.76  tff(c_34, plain, (![A_27, B_28]: (v1_relat_1(k2_zfmisc_1(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.06/1.76  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.06/1.76  tff(c_1552, plain, (![B_220, A_221]: (v1_relat_1(B_220) | ~m1_subset_1(B_220, k1_zfmisc_1(A_221)) | ~v1_relat_1(A_221))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.06/1.76  tff(c_1555, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_1552])).
% 4.06/1.76  tff(c_1558, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1555])).
% 4.06/1.76  tff(c_211, plain, (![B_84, A_85]: (v1_relat_1(B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(A_85)) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.06/1.76  tff(c_214, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_211])).
% 4.06/1.76  tff(c_217, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_214])).
% 4.06/1.76  tff(c_692, plain, (![C_137, B_138, A_139]: (v5_relat_1(C_137, B_138) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.06/1.76  tff(c_706, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_692])).
% 4.06/1.76  tff(c_30, plain, (![B_25, A_24]: (r1_tarski(k2_relat_1(B_25), A_24) | ~v5_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.06/1.76  tff(c_897, plain, (![A_151, B_152, C_153]: (k2_relset_1(A_151, B_152, C_153)=k2_relat_1(C_153) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.06/1.76  tff(c_916, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_897])).
% 4.06/1.76  tff(c_218, plain, (![A_86, B_87]: (r2_hidden('#skF_1'(A_86, B_87), B_87) | r1_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.06/1.76  tff(c_24, plain, (![A_19, B_20]: (m1_subset_1(A_19, B_20) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.06/1.76  tff(c_417, plain, (![A_107, B_108]: (m1_subset_1('#skF_1'(A_107, B_108), B_108) | r1_xboole_0(A_107, B_108))), inference(resolution, [status(thm)], [c_218, c_24])).
% 4.06/1.76  tff(c_171, plain, (![A_77, B_78]: (r2_hidden('#skF_1'(A_77, B_78), A_77) | r1_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.06/1.76  tff(c_46, plain, (![D_50]: (~r2_hidden(D_50, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_50, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.06/1.76  tff(c_187, plain, (![B_78]: (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), B_78), '#skF_4') | r1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), B_78))), inference(resolution, [status(thm)], [c_171, c_46])).
% 4.06/1.76  tff(c_427, plain, (r1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_417, c_187])).
% 4.06/1.76  tff(c_32, plain, (![A_26]: (v1_xboole_0(k1_relat_1(A_26)) | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.06/1.76  tff(c_82, plain, (![A_58, B_59]: (v1_xboole_0(k2_zfmisc_1(A_58, B_59)) | ~v1_xboole_0(B_59))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.06/1.76  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.06/1.76  tff(c_92, plain, (![A_62, B_63]: (k2_zfmisc_1(A_62, B_63)=k1_xboole_0 | ~v1_xboole_0(B_63))), inference(resolution, [status(thm)], [c_82, c_4])).
% 4.06/1.76  tff(c_142, plain, (![A_74, A_75]: (k2_zfmisc_1(A_74, k1_relat_1(A_75))=k1_xboole_0 | ~v1_xboole_0(A_75))), inference(resolution, [status(thm)], [c_32, c_92])).
% 4.06/1.76  tff(c_153, plain, (![A_75]: (v1_relat_1(k1_xboole_0) | ~v1_xboole_0(A_75))), inference(superposition, [status(thm), theory('equality')], [c_142, c_34])).
% 4.06/1.76  tff(c_165, plain, (![A_75]: (~v1_xboole_0(A_75))), inference(splitLeft, [status(thm)], [c_153])).
% 4.06/1.76  tff(c_20, plain, (![B_16, A_15]: (~r1_xboole_0(B_16, A_15) | ~r1_tarski(B_16, A_15) | v1_xboole_0(B_16))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.06/1.76  tff(c_203, plain, (![B_16, A_15]: (~r1_xboole_0(B_16, A_15) | ~r1_tarski(B_16, A_15))), inference(negUnitSimplification, [status(thm)], [c_165, c_20])).
% 4.06/1.76  tff(c_451, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_427, c_203])).
% 4.06/1.76  tff(c_924, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_916, c_451])).
% 4.06/1.76  tff(c_973, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_924])).
% 4.06/1.76  tff(c_977, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_217, c_706, c_973])).
% 4.06/1.76  tff(c_978, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_153])).
% 4.06/1.76  tff(c_1471, plain, (![A_216]: (r1_tarski(A_216, k2_zfmisc_1(k1_relat_1(A_216), k2_relat_1(A_216))) | ~v1_relat_1(A_216))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.06/1.76  tff(c_1046, plain, (![A_166, B_167]: (r2_hidden('#skF_1'(A_166, B_167), A_166) | r1_xboole_0(A_166, B_167))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.06/1.76  tff(c_16, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.06/1.76  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.06/1.76  tff(c_117, plain, (![A_65, B_66, C_67]: (~r1_xboole_0(A_65, B_66) | ~r2_hidden(C_67, k3_xboole_0(A_65, B_66)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.06/1.76  tff(c_121, plain, (![A_68, C_69]: (~r1_xboole_0(A_68, A_68) | ~r2_hidden(C_69, A_68))), inference(superposition, [status(thm), theory('equality')], [c_2, c_117])).
% 4.06/1.76  tff(c_124, plain, (![C_69]: (~r2_hidden(C_69, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_121])).
% 4.06/1.76  tff(c_1067, plain, (![B_170]: (r1_xboole_0(k1_xboole_0, B_170))), inference(resolution, [status(thm)], [c_1046, c_124])).
% 4.06/1.76  tff(c_22, plain, (![A_17, B_18]: (v1_xboole_0(k2_zfmisc_1(A_17, B_18)) | ~v1_xboole_0(B_18))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.06/1.76  tff(c_151, plain, (![A_75]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_relat_1(A_75)) | ~v1_xboole_0(A_75))), inference(superposition, [status(thm), theory('equality')], [c_142, c_22])).
% 4.06/1.76  tff(c_980, plain, (![A_155]: (~v1_xboole_0(k1_relat_1(A_155)) | ~v1_xboole_0(A_155))), inference(splitLeft, [status(thm)], [c_151])).
% 4.06/1.76  tff(c_990, plain, (![A_26]: (~v1_xboole_0(A_26))), inference(resolution, [status(thm)], [c_32, c_980])).
% 4.06/1.76  tff(c_994, plain, (![B_16, A_15]: (~r1_xboole_0(B_16, A_15) | ~r1_tarski(B_16, A_15))), inference(negUnitSimplification, [status(thm)], [c_990, c_20])).
% 4.06/1.76  tff(c_1078, plain, (![B_170]: (~r1_tarski(k1_xboole_0, B_170))), inference(resolution, [status(thm)], [c_1067, c_994])).
% 4.06/1.76  tff(c_1483, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_1471, c_1078])).
% 4.06/1.76  tff(c_1494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_978, c_1483])).
% 4.06/1.76  tff(c_1495, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_151])).
% 4.06/1.76  tff(c_90, plain, (![A_58, B_59]: (k2_zfmisc_1(A_58, B_59)=k1_xboole_0 | ~v1_xboole_0(B_59))), inference(resolution, [status(thm)], [c_82, c_4])).
% 4.06/1.76  tff(c_1509, plain, (![A_58]: (k2_zfmisc_1(A_58, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1495, c_90])).
% 4.06/1.76  tff(c_1676, plain, (![C_237, B_238, A_239]: (v5_relat_1(C_237, B_238) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_239, B_238))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.06/1.76  tff(c_1696, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_1676])).
% 4.06/1.76  tff(c_2425, plain, (![A_292, B_293, C_294]: (k2_relset_1(A_292, B_293, C_294)=k2_relat_1(C_294) | ~m1_subset_1(C_294, k1_zfmisc_1(k2_zfmisc_1(A_292, B_293))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.06/1.76  tff(c_2453, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_2425])).
% 4.06/1.76  tff(c_1562, plain, (![A_222, B_223]: (r2_hidden('#skF_1'(A_222, B_223), B_223) | r1_xboole_0(A_222, B_223))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.06/1.76  tff(c_1581, plain, (![A_222, B_223]: (m1_subset_1('#skF_1'(A_222, B_223), B_223) | r1_xboole_0(A_222, B_223))), inference(resolution, [status(thm)], [c_1562, c_24])).
% 4.06/1.76  tff(c_1582, plain, (![A_224, B_225]: (r2_hidden('#skF_1'(A_224, B_225), A_224) | r1_xboole_0(A_224, B_225))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.06/1.76  tff(c_1729, plain, (![B_244]: (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), B_244), '#skF_4') | r1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), B_244))), inference(resolution, [status(thm)], [c_1582, c_46])).
% 4.06/1.76  tff(c_1734, plain, (r1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_1581, c_1729])).
% 4.06/1.76  tff(c_1804, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_1734, c_20])).
% 4.06/1.76  tff(c_1909, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1804])).
% 4.06/1.76  tff(c_2456, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2453, c_1909])).
% 4.06/1.76  tff(c_2495, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_2456])).
% 4.06/1.76  tff(c_2499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1558, c_1696, c_2495])).
% 4.06/1.76  tff(c_2500, plain, (v1_xboole_0(k2_relset_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_1804])).
% 4.06/1.76  tff(c_2512, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_2500, c_4])).
% 4.06/1.76  tff(c_2812, plain, (![A_320, B_321, C_322]: (k2_relset_1(A_320, B_321, C_322)=k2_relat_1(C_322) | ~m1_subset_1(C_322, k1_zfmisc_1(k2_zfmisc_1(A_320, B_321))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.06/1.76  tff(c_2836, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_2812])).
% 4.06/1.76  tff(c_2841, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2512, c_2836])).
% 4.06/1.76  tff(c_36, plain, (![A_29]: (r1_tarski(A_29, k2_zfmisc_1(k1_relat_1(A_29), k2_relat_1(A_29))) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.06/1.76  tff(c_2848, plain, (r1_tarski('#skF_5', k2_zfmisc_1(k1_relat_1('#skF_5'), k1_xboole_0)) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2841, c_36])).
% 4.06/1.76  tff(c_2860, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1558, c_1509, c_2848])).
% 4.06/1.76  tff(c_1603, plain, (![A_226]: (r1_xboole_0(A_226, k1_xboole_0))), inference(resolution, [status(thm)], [c_1562, c_124])).
% 4.06/1.76  tff(c_1614, plain, (![A_226]: (~r1_tarski(A_226, k1_xboole_0) | v1_xboole_0(A_226))), inference(resolution, [status(thm)], [c_1603, c_20])).
% 4.06/1.76  tff(c_2869, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_2860, c_1614])).
% 4.06/1.76  tff(c_2880, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_2869, c_4])).
% 4.06/1.76  tff(c_48, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.06/1.76  tff(c_2910, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2880, c_48])).
% 4.06/1.76  tff(c_66, plain, (![A_55]: (v1_xboole_0(k1_relat_1(A_55)) | ~v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.06/1.76  tff(c_70, plain, (![A_55]: (k1_relat_1(A_55)=k1_xboole_0 | ~v1_xboole_0(A_55))), inference(resolution, [status(thm)], [c_66, c_4])).
% 4.06/1.76  tff(c_2879, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_2869, c_70])).
% 4.06/1.76  tff(c_2919, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2880, c_2879])).
% 4.06/1.76  tff(c_2934, plain, (![A_323, B_324, C_325]: (k1_relset_1(A_323, B_324, C_325)=k1_relat_1(C_325) | ~m1_subset_1(C_325, k1_zfmisc_1(k2_zfmisc_1(A_323, B_324))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.06/1.76  tff(c_2949, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_2934])).
% 4.06/1.76  tff(c_2954, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2919, c_2949])).
% 4.06/1.76  tff(c_3043, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2910, c_2954])).
% 4.06/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.06/1.76  
% 4.06/1.76  Inference rules
% 4.06/1.76  ----------------------
% 4.06/1.76  #Ref     : 0
% 4.06/1.76  #Sup     : 651
% 4.06/1.76  #Fact    : 0
% 4.06/1.76  #Define  : 0
% 4.06/1.76  #Split   : 4
% 4.06/1.76  #Chain   : 0
% 4.06/1.76  #Close   : 0
% 4.06/1.76  
% 4.06/1.76  Ordering : KBO
% 4.06/1.76  
% 4.06/1.76  Simplification rules
% 4.06/1.76  ----------------------
% 4.06/1.76  #Subsume      : 167
% 4.06/1.76  #Demod        : 345
% 4.06/1.76  #Tautology    : 266
% 4.06/1.76  #SimpNegUnit  : 28
% 4.06/1.76  #BackRed      : 65
% 4.06/1.76  
% 4.06/1.76  #Partial instantiations: 0
% 4.06/1.76  #Strategies tried      : 1
% 4.06/1.76  
% 4.06/1.76  Timing (in seconds)
% 4.06/1.76  ----------------------
% 4.06/1.76  Preprocessing        : 0.34
% 4.06/1.76  Parsing              : 0.19
% 4.06/1.76  CNF conversion       : 0.02
% 4.06/1.76  Main loop            : 0.63
% 4.06/1.76  Inferencing          : 0.23
% 4.38/1.76  Reduction            : 0.20
% 4.38/1.76  Demodulation         : 0.13
% 4.38/1.76  BG Simplification    : 0.03
% 4.38/1.76  Subsumption          : 0.12
% 4.38/1.76  Abstraction          : 0.03
% 4.38/1.76  MUC search           : 0.00
% 4.38/1.76  Cooper               : 0.00
% 4.38/1.76  Total                : 1.02
% 4.38/1.76  Index Insertion      : 0.00
% 4.38/1.76  Index Deletion       : 0.00
% 4.38/1.76  Index Matching       : 0.00
% 4.38/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
