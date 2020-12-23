%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:18 EST 2020

% Result     : Theorem 7.71s
% Output     : CNFRefutation 7.97s
% Verified   : 
% Statistics : Number of formulae       :  251 (5401 expanded)
%              Number of leaves         :   54 (1853 expanded)
%              Depth                    :   19
%              Number of atoms          :  422 (16664 expanded)
%              Number of equality atoms :  130 (5627 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_zfmisc_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k3_subset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_subset_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_7 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_208,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_struct_0(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => ( k1_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(B)
                    & k2_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_64,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_139,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_152,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v1_zfmisc_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc20_struct_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_38,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_172,axiom,(
    ! [A] :
      ( ~ ( ? [B] :
              ( B != k1_xboole_0
              & r2_hidden(B,A) )
          & k3_tarski(A) = k1_xboole_0 )
      & ~ ( k3_tarski(A) != k1_xboole_0
          & ! [B] :
              ~ ( B != k1_xboole_0
                & r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_119,axiom,(
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

tff(f_135,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_184,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_104,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_102,plain,(
    l1_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_34,plain,(
    ! [A_14] : v1_xboole_0('#skF_3'(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_137,plain,(
    ! [A_56] :
      ( k1_xboole_0 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_141,plain,(
    ! [A_14] : '#skF_3'(A_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_137])).

tff(c_142,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_34])).

tff(c_106,plain,(
    l1_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_191,plain,(
    ! [A_63] :
      ( u1_struct_0(A_63) = k2_struct_0(A_63)
      | ~ l1_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_199,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_106,c_191])).

tff(c_198,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_102,c_191])).

tff(c_96,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_200,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),k2_struct_0('#skF_7')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_96])).

tff(c_4141,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_6'),k2_struct_0('#skF_7')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_200])).

tff(c_4146,plain,(
    ! [C_336,A_337,B_338] :
      ( v1_relat_1(C_336)
      | ~ m1_subset_1(C_336,k1_zfmisc_1(k2_zfmisc_1(A_337,B_338))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4162,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_4141,c_4146])).

tff(c_100,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_92,plain,(
    v2_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_46,plain,(
    ! [A_22] :
      ( k2_relat_1(k2_funct_1(A_22)) = k1_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4618,plain,(
    ! [A_387,B_388,C_389] :
      ( k2_relset_1(A_387,B_388,C_389) = k2_relat_1(C_389)
      | ~ m1_subset_1(C_389,k1_zfmisc_1(k2_zfmisc_1(A_387,B_388))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4648,plain,(
    k2_relset_1(k2_struct_0('#skF_6'),k2_struct_0('#skF_7'),'#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_4141,c_4618])).

tff(c_94,plain,(
    k2_relset_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_7'),'#skF_8') = k2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_224,plain,(
    k2_relset_1(k2_struct_0('#skF_6'),k2_struct_0('#skF_7'),'#skF_8') = k2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_198,c_94])).

tff(c_4659,plain,(
    k2_struct_0('#skF_7') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4648,c_224])).

tff(c_4257,plain,(
    ! [A_353] :
      ( m1_subset_1('#skF_4'(A_353),k1_zfmisc_1(u1_struct_0(A_353)))
      | ~ l1_struct_0(A_353)
      | v2_struct_0(A_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_4268,plain,
    ( m1_subset_1('#skF_4'('#skF_7'),k1_zfmisc_1(k2_struct_0('#skF_7')))
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_4257])).

tff(c_4274,plain,
    ( m1_subset_1('#skF_4'('#skF_7'),k1_zfmisc_1(k2_struct_0('#skF_7')))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_4268])).

tff(c_4275,plain,(
    m1_subset_1('#skF_4'('#skF_7'),k1_zfmisc_1(k2_struct_0('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_4274])).

tff(c_24,plain,(
    ! [B_9,A_8] :
      ( v1_xboole_0(B_9)
      | ~ m1_subset_1(B_9,A_8)
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4283,plain,
    ( v1_xboole_0('#skF_4'('#skF_7'))
    | ~ v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_4275,c_24])).

tff(c_4285,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_4283])).

tff(c_4167,plain,(
    ! [B_341,A_342] :
      ( r2_hidden(B_341,A_342)
      | ~ m1_subset_1(B_341,A_342)
      | v1_xboole_0(A_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [C_6,A_2] :
      ( r1_tarski(C_6,A_2)
      | ~ r2_hidden(C_6,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4334,plain,(
    ! [B_363,A_364] :
      ( r1_tarski(B_363,A_364)
      | ~ m1_subset_1(B_363,k1_zfmisc_1(A_364))
      | v1_xboole_0(k1_zfmisc_1(A_364)) ) ),
    inference(resolution,[status(thm)],[c_4167,c_4])).

tff(c_4340,plain,
    ( r1_tarski('#skF_4'('#skF_7'),k2_struct_0('#skF_7'))
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_4275,c_4334])).

tff(c_4364,plain,(
    r1_tarski('#skF_4'('#skF_7'),k2_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_4285,c_4340])).

tff(c_16,plain,(
    ! [A_7] : k3_tarski(k1_zfmisc_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [C_6,A_2] :
      ( r2_hidden(C_6,k1_zfmisc_1(A_2))
      | ~ r1_tarski(C_6,A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_250,plain,(
    ! [A_79,B_80] :
      ( k3_tarski(A_79) != k1_xboole_0
      | ~ r2_hidden(B_80,A_79)
      | k1_xboole_0 = B_80 ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_253,plain,(
    ! [A_2,C_6] :
      ( k3_tarski(k1_zfmisc_1(A_2)) != k1_xboole_0
      | k1_xboole_0 = C_6
      | ~ r1_tarski(C_6,A_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_250])).

tff(c_258,plain,(
    ! [A_2,C_6] :
      ( k1_xboole_0 != A_2
      | k1_xboole_0 = C_6
      | ~ r1_tarski(C_6,A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_253])).

tff(c_4378,plain,
    ( k2_struct_0('#skF_7') != k1_xboole_0
    | '#skF_4'('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4364,c_258])).

tff(c_4451,plain,(
    k2_struct_0('#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4378])).

tff(c_4668,plain,(
    k2_relat_1('#skF_8') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4659,c_4451])).

tff(c_98,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_6'),u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_201,plain,(
    v1_funct_2('#skF_8',u1_struct_0('#skF_6'),k2_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_98])).

tff(c_213,plain,(
    v1_funct_2('#skF_8',k2_struct_0('#skF_6'),k2_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_201])).

tff(c_4677,plain,(
    v1_funct_2('#skF_8',k2_struct_0('#skF_6'),k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4659,c_213])).

tff(c_4552,plain,(
    ! [A_376,B_377,C_378] :
      ( k1_relset_1(A_376,B_377,C_378) = k1_relat_1(C_378)
      | ~ m1_subset_1(C_378,k1_zfmisc_1(k2_zfmisc_1(A_376,B_377))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4582,plain,(
    k1_relset_1(k2_struct_0('#skF_6'),k2_struct_0('#skF_7'),'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_4141,c_4552])).

tff(c_4665,plain,(
    k1_relset_1(k2_struct_0('#skF_6'),k2_relat_1('#skF_8'),'#skF_8') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4659,c_4582])).

tff(c_4676,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_6'),k2_relat_1('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4659,c_4141])).

tff(c_5340,plain,(
    ! [B_440,A_441,C_442] :
      ( k1_xboole_0 = B_440
      | k1_relset_1(A_441,B_440,C_442) = A_441
      | ~ v1_funct_2(C_442,A_441,B_440)
      | ~ m1_subset_1(C_442,k1_zfmisc_1(k2_zfmisc_1(A_441,B_440))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_5343,plain,
    ( k2_relat_1('#skF_8') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_6'),k2_relat_1('#skF_8'),'#skF_8') = k2_struct_0('#skF_6')
    | ~ v1_funct_2('#skF_8',k2_struct_0('#skF_6'),k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_4676,c_5340])).

tff(c_5366,plain,
    ( k2_relat_1('#skF_8') = k1_xboole_0
    | k2_struct_0('#skF_6') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4677,c_4665,c_5343])).

tff(c_5367,plain,(
    k2_struct_0('#skF_6') = k1_relat_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_4668,c_5366])).

tff(c_5387,plain,(
    v1_funct_2('#skF_8',k1_relat_1('#skF_8'),k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5367,c_4677])).

tff(c_4664,plain,(
    k2_relset_1(k2_struct_0('#skF_6'),k2_relat_1('#skF_8'),'#skF_8') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4659,c_4648])).

tff(c_5382,plain,(
    k2_relset_1(k1_relat_1('#skF_8'),k2_relat_1('#skF_8'),'#skF_8') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5367,c_4664])).

tff(c_5385,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'),k2_relat_1('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5367,c_4676])).

tff(c_5832,plain,(
    ! [C_474,B_475,A_476] :
      ( m1_subset_1(k2_funct_1(C_474),k1_zfmisc_1(k2_zfmisc_1(B_475,A_476)))
      | k2_relset_1(A_476,B_475,C_474) != B_475
      | ~ v2_funct_1(C_474)
      | ~ m1_subset_1(C_474,k1_zfmisc_1(k2_zfmisc_1(A_476,B_475)))
      | ~ v1_funct_2(C_474,A_476,B_475)
      | ~ v1_funct_1(C_474) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_54,plain,(
    ! [A_29,B_30,C_31] :
      ( k2_relset_1(A_29,B_30,C_31) = k2_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_8013,plain,(
    ! [B_588,A_589,C_590] :
      ( k2_relset_1(B_588,A_589,k2_funct_1(C_590)) = k2_relat_1(k2_funct_1(C_590))
      | k2_relset_1(A_589,B_588,C_590) != B_588
      | ~ v2_funct_1(C_590)
      | ~ m1_subset_1(C_590,k1_zfmisc_1(k2_zfmisc_1(A_589,B_588)))
      | ~ v1_funct_2(C_590,A_589,B_588)
      | ~ v1_funct_1(C_590) ) ),
    inference(resolution,[status(thm)],[c_5832,c_54])).

tff(c_8031,plain,
    ( k2_relset_1(k2_relat_1('#skF_8'),k1_relat_1('#skF_8'),k2_funct_1('#skF_8')) = k2_relat_1(k2_funct_1('#skF_8'))
    | k2_relset_1(k1_relat_1('#skF_8'),k2_relat_1('#skF_8'),'#skF_8') != k2_relat_1('#skF_8')
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_2('#skF_8',k1_relat_1('#skF_8'),k2_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_5385,c_8013])).

tff(c_8064,plain,(
    k2_relset_1(k2_relat_1('#skF_8'),k1_relat_1('#skF_8'),k2_funct_1('#skF_8')) = k2_relat_1(k2_funct_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_5387,c_92,c_5382,c_8031])).

tff(c_5783,plain,(
    ! [A_471,B_472,C_473] :
      ( k2_tops_2(A_471,B_472,C_473) = k2_funct_1(C_473)
      | ~ v2_funct_1(C_473)
      | k2_relset_1(A_471,B_472,C_473) != B_472
      | ~ m1_subset_1(C_473,k1_zfmisc_1(k2_zfmisc_1(A_471,B_472)))
      | ~ v1_funct_2(C_473,A_471,B_472)
      | ~ v1_funct_1(C_473) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_5786,plain,
    ( k2_tops_2(k1_relat_1('#skF_8'),k2_relat_1('#skF_8'),'#skF_8') = k2_funct_1('#skF_8')
    | ~ v2_funct_1('#skF_8')
    | k2_relset_1(k1_relat_1('#skF_8'),k2_relat_1('#skF_8'),'#skF_8') != k2_relat_1('#skF_8')
    | ~ v1_funct_2('#skF_8',k1_relat_1('#skF_8'),k2_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_5385,c_5783])).

tff(c_5809,plain,(
    k2_tops_2(k1_relat_1('#skF_8'),k2_relat_1('#skF_8'),'#skF_8') = k2_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_5387,c_5382,c_92,c_5786])).

tff(c_349,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_6'),k2_struct_0('#skF_7')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_200])).

tff(c_50,plain,(
    ! [C_25,A_23,B_24] :
      ( v1_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_359,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_349,c_50])).

tff(c_48,plain,(
    ! [A_22] :
      ( k1_relat_1(k2_funct_1(A_22)) = k2_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_633,plain,(
    ! [A_121,B_122,C_123] :
      ( k2_relset_1(A_121,B_122,C_123) = k2_relat_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_663,plain,(
    k2_relset_1(k2_struct_0('#skF_6'),k2_struct_0('#skF_7'),'#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_349,c_633])).

tff(c_697,plain,(
    k2_struct_0('#skF_7') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_224])).

tff(c_397,plain,(
    ! [A_102] :
      ( m1_subset_1('#skF_4'(A_102),k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_struct_0(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_408,plain,
    ( m1_subset_1('#skF_4'('#skF_7'),k1_zfmisc_1(k2_struct_0('#skF_7')))
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_397])).

tff(c_414,plain,
    ( m1_subset_1('#skF_4'('#skF_7'),k1_zfmisc_1(k2_struct_0('#skF_7')))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_408])).

tff(c_415,plain,(
    m1_subset_1('#skF_4'('#skF_7'),k1_zfmisc_1(k2_struct_0('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_414])).

tff(c_422,plain,
    ( v1_xboole_0('#skF_4'('#skF_7'))
    | ~ v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_415,c_24])).

tff(c_424,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_422])).

tff(c_299,plain,(
    ! [B_90,A_91] :
      ( r2_hidden(B_90,A_91)
      | ~ m1_subset_1(B_90,A_91)
      | v1_xboole_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_438,plain,(
    ! [B_106,A_107] :
      ( r1_tarski(B_106,A_107)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_107))
      | v1_xboole_0(k1_zfmisc_1(A_107)) ) ),
    inference(resolution,[status(thm)],[c_299,c_4])).

tff(c_441,plain,
    ( r1_tarski('#skF_4'('#skF_7'),k2_struct_0('#skF_7'))
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_415,c_438])).

tff(c_464,plain,(
    r1_tarski('#skF_4'('#skF_7'),k2_struct_0('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_424,c_441])).

tff(c_478,plain,
    ( k2_struct_0('#skF_7') != k1_xboole_0
    | '#skF_4'('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_464,c_258])).

tff(c_550,plain,(
    k2_struct_0('#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_478])).

tff(c_705,plain,(
    k2_relat_1('#skF_8') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_697,c_550])).

tff(c_713,plain,(
    v1_funct_2('#skF_8',k2_struct_0('#skF_6'),k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_697,c_213])).

tff(c_712,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_6'),k2_relat_1('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_697,c_349])).

tff(c_52,plain,(
    ! [A_26,B_27,C_28] :
      ( k1_relset_1(A_26,B_27,C_28) = k1_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_843,plain,(
    k1_relset_1(k2_struct_0('#skF_6'),k2_relat_1('#skF_8'),'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_712,c_52])).

tff(c_1414,plain,(
    ! [B_182,A_183,C_184] :
      ( k1_xboole_0 = B_182
      | k1_relset_1(A_183,B_182,C_184) = A_183
      | ~ v1_funct_2(C_184,A_183,B_182)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_183,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1417,plain,
    ( k2_relat_1('#skF_8') = k1_xboole_0
    | k1_relset_1(k2_struct_0('#skF_6'),k2_relat_1('#skF_8'),'#skF_8') = k2_struct_0('#skF_6')
    | ~ v1_funct_2('#skF_8',k2_struct_0('#skF_6'),k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_712,c_1414])).

tff(c_1440,plain,
    ( k2_relat_1('#skF_8') = k1_xboole_0
    | k2_struct_0('#skF_6') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_713,c_843,c_1417])).

tff(c_1441,plain,(
    k2_struct_0('#skF_6') = k1_relat_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_705,c_1440])).

tff(c_1460,plain,(
    v1_funct_2('#skF_8',k1_relat_1('#skF_8'),k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1441,c_713])).

tff(c_702,plain,(
    k2_relset_1(k2_struct_0('#skF_6'),k2_relat_1('#skF_8'),'#skF_8') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_697,c_663])).

tff(c_1455,plain,(
    k2_relset_1(k1_relat_1('#skF_8'),k2_relat_1('#skF_8'),'#skF_8') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1441,c_702])).

tff(c_1456,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'),k2_relat_1('#skF_8')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1441,c_712])).

tff(c_1864,plain,(
    ! [C_220,B_221,A_222] :
      ( m1_subset_1(k2_funct_1(C_220),k1_zfmisc_1(k2_zfmisc_1(B_221,A_222)))
      | k2_relset_1(A_222,B_221,C_220) != B_221
      | ~ v2_funct_1(C_220)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(k2_zfmisc_1(A_222,B_221)))
      | ~ v1_funct_2(C_220,A_222,B_221)
      | ~ v1_funct_1(C_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_3791,plain,(
    ! [B_320,A_321,C_322] :
      ( k1_relset_1(B_320,A_321,k2_funct_1(C_322)) = k1_relat_1(k2_funct_1(C_322))
      | k2_relset_1(A_321,B_320,C_322) != B_320
      | ~ v2_funct_1(C_322)
      | ~ m1_subset_1(C_322,k1_zfmisc_1(k2_zfmisc_1(A_321,B_320)))
      | ~ v1_funct_2(C_322,A_321,B_320)
      | ~ v1_funct_1(C_322) ) ),
    inference(resolution,[status(thm)],[c_1864,c_52])).

tff(c_3809,plain,
    ( k1_relset_1(k2_relat_1('#skF_8'),k1_relat_1('#skF_8'),k2_funct_1('#skF_8')) = k1_relat_1(k2_funct_1('#skF_8'))
    | k2_relset_1(k1_relat_1('#skF_8'),k2_relat_1('#skF_8'),'#skF_8') != k2_relat_1('#skF_8')
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_2('#skF_8',k1_relat_1('#skF_8'),k2_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1456,c_3791])).

tff(c_3842,plain,(
    k1_relset_1(k2_relat_1('#skF_8'),k1_relat_1('#skF_8'),k2_funct_1('#skF_8')) = k1_relat_1(k2_funct_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1460,c_92,c_1455,c_3809])).

tff(c_1751,plain,(
    ! [A_209,B_210,C_211] :
      ( k2_tops_2(A_209,B_210,C_211) = k2_funct_1(C_211)
      | ~ v2_funct_1(C_211)
      | k2_relset_1(A_209,B_210,C_211) != B_210
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210)))
      | ~ v1_funct_2(C_211,A_209,B_210)
      | ~ v1_funct_1(C_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_1754,plain,
    ( k2_tops_2(k1_relat_1('#skF_8'),k2_relat_1('#skF_8'),'#skF_8') = k2_funct_1('#skF_8')
    | ~ v2_funct_1('#skF_8')
    | k2_relset_1(k1_relat_1('#skF_8'),k2_relat_1('#skF_8'),'#skF_8') != k2_relat_1('#skF_8')
    | ~ v1_funct_2('#skF_8',k1_relat_1('#skF_8'),k2_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1456,c_1751])).

tff(c_1777,plain,(
    k2_tops_2(k1_relat_1('#skF_8'),k2_relat_1('#skF_8'),'#skF_8') = k2_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1460,c_1455,c_92,c_1754])).

tff(c_90,plain,
    ( k2_relset_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_6'),k2_tops_2(u1_struct_0('#skF_6'),u1_struct_0('#skF_7'),'#skF_8')) != k2_struct_0('#skF_6')
    | k1_relset_1(u1_struct_0('#skF_7'),u1_struct_0('#skF_6'),k2_tops_2(u1_struct_0('#skF_6'),u1_struct_0('#skF_7'),'#skF_8')) != k2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_271,plain,
    ( k2_relset_1(k2_struct_0('#skF_7'),k2_struct_0('#skF_6'),k2_tops_2(k2_struct_0('#skF_6'),k2_struct_0('#skF_7'),'#skF_8')) != k2_struct_0('#skF_6')
    | k1_relset_1(k2_struct_0('#skF_7'),k2_struct_0('#skF_6'),k2_tops_2(k2_struct_0('#skF_6'),k2_struct_0('#skF_7'),'#skF_8')) != k2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_199,c_198,c_198,c_199,c_199,c_198,c_198,c_90])).

tff(c_272,plain,(
    k1_relset_1(k2_struct_0('#skF_7'),k2_struct_0('#skF_6'),k2_tops_2(k2_struct_0('#skF_6'),k2_struct_0('#skF_7'),'#skF_8')) != k2_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_271])).

tff(c_707,plain,(
    k1_relset_1(k2_relat_1('#skF_8'),k2_struct_0('#skF_6'),k2_tops_2(k2_struct_0('#skF_6'),k2_relat_1('#skF_8'),'#skF_8')) != k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_697,c_697,c_697,c_272])).

tff(c_1453,plain,(
    k1_relset_1(k2_relat_1('#skF_8'),k1_relat_1('#skF_8'),k2_tops_2(k1_relat_1('#skF_8'),k2_relat_1('#skF_8'),'#skF_8')) != k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1441,c_1441,c_707])).

tff(c_1789,plain,(
    k1_relset_1(k2_relat_1('#skF_8'),k1_relat_1('#skF_8'),k2_funct_1('#skF_8')) != k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1777,c_1453])).

tff(c_3854,plain,(
    k1_relat_1(k2_funct_1('#skF_8')) != k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3842,c_1789])).

tff(c_3861,plain,
    ( ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_3854])).

tff(c_3865,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_100,c_92,c_3861])).

tff(c_3867,plain,(
    k2_struct_0('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_478])).

tff(c_44,plain,(
    ! [C_21,B_20,A_19] :
      ( ~ v1_xboole_0(C_21)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(C_21))
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_421,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_7'))
      | ~ r2_hidden(A_19,'#skF_4'('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_415,c_44])).

tff(c_423,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_421])).

tff(c_3872,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3867,c_423])).

tff(c_3880,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_3872])).

tff(c_3882,plain,(
    v1_xboole_0(k2_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_421])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3891,plain,(
    k2_struct_0('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3882,c_2])).

tff(c_3883,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_422])).

tff(c_3924,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3891,c_3883])).

tff(c_3897,plain,(
    u1_struct_0('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3891,c_198])).

tff(c_80,plain,(
    ! [A_39] :
      ( m1_subset_1('#skF_4'(A_39),k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ l1_struct_0(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_3906,plain,
    ( m1_subset_1('#skF_4'('#skF_7'),k1_zfmisc_1(k1_xboole_0))
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_3897,c_80])).

tff(c_3910,plain,
    ( m1_subset_1('#skF_4'('#skF_7'),k1_zfmisc_1(k1_xboole_0))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_3906])).

tff(c_3911,plain,(
    m1_subset_1('#skF_4'('#skF_7'),k1_zfmisc_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_3910])).

tff(c_4019,plain,(
    ! [B_331,A_332] :
      ( r1_tarski(B_331,A_332)
      | ~ m1_subset_1(B_331,k1_zfmisc_1(A_332))
      | v1_xboole_0(k1_zfmisc_1(A_332)) ) ),
    inference(resolution,[status(thm)],[c_299,c_4])).

tff(c_4025,plain,
    ( r1_tarski('#skF_4'('#skF_7'),k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_3911,c_4019])).

tff(c_4048,plain,(
    r1_tarski('#skF_4'('#skF_7'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_3924,c_4025])).

tff(c_4059,plain,(
    '#skF_4'('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4048,c_258])).

tff(c_22,plain,(
    ! [B_9,A_8] :
      ( m1_subset_1(B_9,A_8)
      | ~ v1_xboole_0(B_9)
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [B_9,A_8] :
      ( r2_hidden(B_9,A_8)
      | ~ m1_subset_1(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3913,plain,(
    ! [A_323] : ~ r2_hidden(A_323,'#skF_4'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_421])).

tff(c_3922,plain,(
    ! [B_9] :
      ( ~ m1_subset_1(B_9,'#skF_4'('#skF_7'))
      | v1_xboole_0('#skF_4'('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_20,c_3913])).

tff(c_3962,plain,(
    ! [B_325] : ~ m1_subset_1(B_325,'#skF_4'('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_3922])).

tff(c_3973,plain,(
    ! [B_9] :
      ( ~ v1_xboole_0(B_9)
      | ~ v1_xboole_0('#skF_4'('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_22,c_3962])).

tff(c_3974,plain,(
    ~ v1_xboole_0('#skF_4'('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_3973])).

tff(c_4061,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4059,c_3974])).

tff(c_4069,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_4061])).

tff(c_4070,plain,(
    ! [B_9] : ~ v1_xboole_0(B_9) ),
    inference(splitRight,[status(thm)],[c_3973])).

tff(c_4078,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4070,c_142])).

tff(c_4079,plain,(
    v1_xboole_0('#skF_4'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_3922])).

tff(c_78,plain,(
    ! [A_39] :
      ( ~ v1_xboole_0('#skF_4'(A_39))
      | ~ l1_struct_0(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_4085,plain,
    ( ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_4079,c_78])).

tff(c_4093,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_4085])).

tff(c_4095,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_4093])).

tff(c_4096,plain,(
    v1_xboole_0('#skF_4'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_422])).

tff(c_4120,plain,
    ( ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_4096,c_78])).

tff(c_4127,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_4120])).

tff(c_4129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_4127])).

tff(c_4130,plain,(
    k2_relset_1(k2_struct_0('#skF_7'),k2_struct_0('#skF_6'),k2_tops_2(k2_struct_0('#skF_6'),k2_struct_0('#skF_7'),'#skF_8')) != k2_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_271])).

tff(c_4675,plain,(
    k2_relset_1(k2_relat_1('#skF_8'),k2_struct_0('#skF_6'),k2_tops_2(k2_struct_0('#skF_6'),k2_relat_1('#skF_8'),'#skF_8')) != k2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4659,c_4659,c_4130])).

tff(c_5379,plain,(
    k2_relset_1(k2_relat_1('#skF_8'),k1_relat_1('#skF_8'),k2_tops_2(k1_relat_1('#skF_8'),k2_relat_1('#skF_8'),'#skF_8')) != k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5367,c_5367,c_5367,c_4675])).

tff(c_5822,plain,(
    k2_relset_1(k2_relat_1('#skF_8'),k1_relat_1('#skF_8'),k2_funct_1('#skF_8')) != k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5809,c_5379])).

tff(c_8076,plain,(
    k2_relat_1(k2_funct_1('#skF_8')) != k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8064,c_5822])).

tff(c_8083,plain,
    ( ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_8076])).

tff(c_8087,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4162,c_100,c_92,c_8083])).

tff(c_8089,plain,(
    k2_struct_0('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4378])).

tff(c_4282,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_7'))
      | ~ r2_hidden(A_19,'#skF_4'('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_4275,c_44])).

tff(c_4284,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_4282])).

tff(c_8094,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8089,c_4284])).

tff(c_8103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_8094])).

tff(c_8105,plain,(
    v1_xboole_0(k2_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_4282])).

tff(c_8114,plain,(
    k2_struct_0('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8105,c_2])).

tff(c_8106,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_4283])).

tff(c_8148,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8114,c_8106])).

tff(c_8121,plain,(
    u1_struct_0('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8114,c_198])).

tff(c_8130,plain,
    ( m1_subset_1('#skF_4'('#skF_7'),k1_zfmisc_1(k1_xboole_0))
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_8121,c_80])).

tff(c_8134,plain,
    ( m1_subset_1('#skF_4'('#skF_7'),k1_zfmisc_1(k1_xboole_0))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_8130])).

tff(c_8135,plain,(
    m1_subset_1('#skF_4'('#skF_7'),k1_zfmisc_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_8134])).

tff(c_82,plain,(
    ! [A_41,B_44] :
      ( k3_tarski(A_41) != k1_xboole_0
      | ~ r2_hidden(B_44,A_41)
      | k1_xboole_0 = B_44 ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_8271,plain,(
    ! [A_602,B_603] :
      ( k3_tarski(A_602) != k1_xboole_0
      | k1_xboole_0 = B_603
      | ~ m1_subset_1(B_603,A_602)
      | v1_xboole_0(A_602) ) ),
    inference(resolution,[status(thm)],[c_4167,c_82])).

tff(c_8280,plain,
    ( k3_tarski(k1_zfmisc_1(k1_xboole_0)) != k1_xboole_0
    | '#skF_4'('#skF_7') = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_8135,c_8271])).

tff(c_8303,plain,
    ( '#skF_4'('#skF_7') = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_8280])).

tff(c_8304,plain,(
    '#skF_4'('#skF_7') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_8148,c_8303])).

tff(c_8137,plain,(
    ! [A_591] : ~ r2_hidden(A_591,'#skF_4'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_4282])).

tff(c_8146,plain,(
    ! [B_9] :
      ( ~ m1_subset_1(B_9,'#skF_4'('#skF_7'))
      | v1_xboole_0('#skF_4'('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_20,c_8137])).

tff(c_8192,plain,(
    ! [B_594] : ~ m1_subset_1(B_594,'#skF_4'('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_8146])).

tff(c_8203,plain,(
    ! [B_9] :
      ( ~ v1_xboole_0(B_9)
      | ~ v1_xboole_0('#skF_4'('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_22,c_8192])).

tff(c_8204,plain,(
    ~ v1_xboole_0('#skF_4'('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_8203])).

tff(c_8314,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8304,c_8204])).

tff(c_8321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_8314])).

tff(c_8322,plain,(
    ! [B_9] : ~ v1_xboole_0(B_9) ),
    inference(splitRight,[status(thm)],[c_8203])).

tff(c_8330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8322,c_142])).

tff(c_8331,plain,(
    v1_xboole_0('#skF_4'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_8146])).

tff(c_8337,plain,
    ( ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_8331,c_78])).

tff(c_8345,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_8337])).

tff(c_8347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_8345])).

tff(c_8348,plain,(
    v1_xboole_0('#skF_4'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_4283])).

tff(c_8378,plain,
    ( ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_8348,c_78])).

tff(c_8385,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_8378])).

tff(c_8387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_8385])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:33:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.71/2.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.71/2.66  
% 7.71/2.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.71/2.66  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_zfmisc_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k3_subset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_subset_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_7 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1
% 7.71/2.66  
% 7.71/2.66  %Foreground sorts:
% 7.71/2.66  
% 7.71/2.66  
% 7.71/2.66  %Background operators:
% 7.71/2.66  
% 7.71/2.66  
% 7.71/2.66  %Foreground operators:
% 7.71/2.66  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.71/2.66  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.71/2.66  tff('#skF_5', type, '#skF_5': $i > $i).
% 7.71/2.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.71/2.66  tff('#skF_4', type, '#skF_4': $i > $i).
% 7.71/2.66  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.71/2.66  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.71/2.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.71/2.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.71/2.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.71/2.66  tff('#skF_7', type, '#skF_7': $i).
% 7.71/2.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.71/2.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.71/2.66  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 7.71/2.66  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 7.71/2.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.71/2.66  tff('#skF_6', type, '#skF_6': $i).
% 7.71/2.66  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.71/2.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.71/2.66  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.71/2.66  tff('#skF_8', type, '#skF_8': $i).
% 7.71/2.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.71/2.66  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.71/2.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.71/2.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.71/2.66  tff('#skF_3', type, '#skF_3': $i > $i).
% 7.71/2.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.71/2.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.71/2.66  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 7.71/2.66  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 7.71/2.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.71/2.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.71/2.66  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 7.71/2.66  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.71/2.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.71/2.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.71/2.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.71/2.66  
% 7.97/2.70  tff(f_208, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 7.97/2.70  tff(f_64, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 7.97/2.70  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 7.97/2.70  tff(f_139, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 7.97/2.70  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.97/2.70  tff(f_89, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 7.97/2.70  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.97/2.70  tff(f_152, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v1_zfmisc_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc20_struct_0)).
% 7.97/2.70  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 7.97/2.70  tff(f_36, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 7.97/2.70  tff(f_38, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 7.97/2.70  tff(f_172, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_orders_1)).
% 7.97/2.70  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.97/2.70  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.97/2.70  tff(f_135, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 7.97/2.70  tff(f_184, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 7.97/2.70  tff(f_79, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 7.97/2.70  tff(c_104, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.97/2.70  tff(c_102, plain, (l1_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.97/2.70  tff(c_34, plain, (![A_14]: (v1_xboole_0('#skF_3'(A_14)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.97/2.70  tff(c_137, plain, (![A_56]: (k1_xboole_0=A_56 | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.97/2.70  tff(c_141, plain, (![A_14]: ('#skF_3'(A_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_137])).
% 7.97/2.70  tff(c_142, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_141, c_34])).
% 7.97/2.70  tff(c_106, plain, (l1_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.97/2.70  tff(c_191, plain, (![A_63]: (u1_struct_0(A_63)=k2_struct_0(A_63) | ~l1_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.97/2.70  tff(c_199, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_106, c_191])).
% 7.97/2.70  tff(c_198, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_102, c_191])).
% 7.97/2.70  tff(c_96, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.97/2.70  tff(c_200, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), k2_struct_0('#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_96])).
% 7.97/2.70  tff(c_4141, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_200])).
% 7.97/2.70  tff(c_4146, plain, (![C_336, A_337, B_338]: (v1_relat_1(C_336) | ~m1_subset_1(C_336, k1_zfmisc_1(k2_zfmisc_1(A_337, B_338))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.97/2.70  tff(c_4162, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_4141, c_4146])).
% 7.97/2.70  tff(c_100, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.97/2.70  tff(c_92, plain, (v2_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.97/2.70  tff(c_46, plain, (![A_22]: (k2_relat_1(k2_funct_1(A_22))=k1_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.97/2.70  tff(c_4618, plain, (![A_387, B_388, C_389]: (k2_relset_1(A_387, B_388, C_389)=k2_relat_1(C_389) | ~m1_subset_1(C_389, k1_zfmisc_1(k2_zfmisc_1(A_387, B_388))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.97/2.70  tff(c_4648, plain, (k2_relset_1(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'), '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_4141, c_4618])).
% 7.97/2.70  tff(c_94, plain, (k2_relset_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_7'), '#skF_8')=k2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.97/2.70  tff(c_224, plain, (k2_relset_1(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'), '#skF_8')=k2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_198, c_94])).
% 7.97/2.70  tff(c_4659, plain, (k2_struct_0('#skF_7')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4648, c_224])).
% 7.97/2.70  tff(c_4257, plain, (![A_353]: (m1_subset_1('#skF_4'(A_353), k1_zfmisc_1(u1_struct_0(A_353))) | ~l1_struct_0(A_353) | v2_struct_0(A_353))), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.97/2.70  tff(c_4268, plain, (m1_subset_1('#skF_4'('#skF_7'), k1_zfmisc_1(k2_struct_0('#skF_7'))) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_198, c_4257])).
% 7.97/2.70  tff(c_4274, plain, (m1_subset_1('#skF_4'('#skF_7'), k1_zfmisc_1(k2_struct_0('#skF_7'))) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_4268])).
% 7.97/2.70  tff(c_4275, plain, (m1_subset_1('#skF_4'('#skF_7'), k1_zfmisc_1(k2_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_104, c_4274])).
% 7.97/2.70  tff(c_24, plain, (![B_9, A_8]: (v1_xboole_0(B_9) | ~m1_subset_1(B_9, A_8) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.97/2.70  tff(c_4283, plain, (v1_xboole_0('#skF_4'('#skF_7')) | ~v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_4275, c_24])).
% 7.97/2.70  tff(c_4285, plain, (~v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_7')))), inference(splitLeft, [status(thm)], [c_4283])).
% 7.97/2.70  tff(c_4167, plain, (![B_341, A_342]: (r2_hidden(B_341, A_342) | ~m1_subset_1(B_341, A_342) | v1_xboole_0(A_342))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.97/2.70  tff(c_4, plain, (![C_6, A_2]: (r1_tarski(C_6, A_2) | ~r2_hidden(C_6, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.97/2.70  tff(c_4334, plain, (![B_363, A_364]: (r1_tarski(B_363, A_364) | ~m1_subset_1(B_363, k1_zfmisc_1(A_364)) | v1_xboole_0(k1_zfmisc_1(A_364)))), inference(resolution, [status(thm)], [c_4167, c_4])).
% 7.97/2.70  tff(c_4340, plain, (r1_tarski('#skF_4'('#skF_7'), k2_struct_0('#skF_7')) | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_4275, c_4334])).
% 7.97/2.70  tff(c_4364, plain, (r1_tarski('#skF_4'('#skF_7'), k2_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_4285, c_4340])).
% 7.97/2.70  tff(c_16, plain, (![A_7]: (k3_tarski(k1_zfmisc_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.97/2.70  tff(c_6, plain, (![C_6, A_2]: (r2_hidden(C_6, k1_zfmisc_1(A_2)) | ~r1_tarski(C_6, A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.97/2.70  tff(c_250, plain, (![A_79, B_80]: (k3_tarski(A_79)!=k1_xboole_0 | ~r2_hidden(B_80, A_79) | k1_xboole_0=B_80)), inference(cnfTransformation, [status(thm)], [f_172])).
% 7.97/2.70  tff(c_253, plain, (![A_2, C_6]: (k3_tarski(k1_zfmisc_1(A_2))!=k1_xboole_0 | k1_xboole_0=C_6 | ~r1_tarski(C_6, A_2))), inference(resolution, [status(thm)], [c_6, c_250])).
% 7.97/2.70  tff(c_258, plain, (![A_2, C_6]: (k1_xboole_0!=A_2 | k1_xboole_0=C_6 | ~r1_tarski(C_6, A_2))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_253])).
% 7.97/2.70  tff(c_4378, plain, (k2_struct_0('#skF_7')!=k1_xboole_0 | '#skF_4'('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_4364, c_258])).
% 7.97/2.70  tff(c_4451, plain, (k2_struct_0('#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_4378])).
% 7.97/2.70  tff(c_4668, plain, (k2_relat_1('#skF_8')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4659, c_4451])).
% 7.97/2.70  tff(c_98, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_6'), u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.97/2.70  tff(c_201, plain, (v1_funct_2('#skF_8', u1_struct_0('#skF_6'), k2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_98])).
% 7.97/2.70  tff(c_213, plain, (v1_funct_2('#skF_8', k2_struct_0('#skF_6'), k2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_201])).
% 7.97/2.70  tff(c_4677, plain, (v1_funct_2('#skF_8', k2_struct_0('#skF_6'), k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_4659, c_213])).
% 7.97/2.70  tff(c_4552, plain, (![A_376, B_377, C_378]: (k1_relset_1(A_376, B_377, C_378)=k1_relat_1(C_378) | ~m1_subset_1(C_378, k1_zfmisc_1(k2_zfmisc_1(A_376, B_377))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.97/2.70  tff(c_4582, plain, (k1_relset_1(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'), '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_4141, c_4552])).
% 7.97/2.70  tff(c_4665, plain, (k1_relset_1(k2_struct_0('#skF_6'), k2_relat_1('#skF_8'), '#skF_8')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4659, c_4582])).
% 7.97/2.70  tff(c_4676, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_6'), k2_relat_1('#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_4659, c_4141])).
% 7.97/2.70  tff(c_5340, plain, (![B_440, A_441, C_442]: (k1_xboole_0=B_440 | k1_relset_1(A_441, B_440, C_442)=A_441 | ~v1_funct_2(C_442, A_441, B_440) | ~m1_subset_1(C_442, k1_zfmisc_1(k2_zfmisc_1(A_441, B_440))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.97/2.70  tff(c_5343, plain, (k2_relat_1('#skF_8')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_6'), k2_relat_1('#skF_8'), '#skF_8')=k2_struct_0('#skF_6') | ~v1_funct_2('#skF_8', k2_struct_0('#skF_6'), k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_4676, c_5340])).
% 7.97/2.70  tff(c_5366, plain, (k2_relat_1('#skF_8')=k1_xboole_0 | k2_struct_0('#skF_6')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4677, c_4665, c_5343])).
% 7.97/2.70  tff(c_5367, plain, (k2_struct_0('#skF_6')=k1_relat_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_4668, c_5366])).
% 7.97/2.70  tff(c_5387, plain, (v1_funct_2('#skF_8', k1_relat_1('#skF_8'), k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_5367, c_4677])).
% 7.97/2.70  tff(c_4664, plain, (k2_relset_1(k2_struct_0('#skF_6'), k2_relat_1('#skF_8'), '#skF_8')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4659, c_4648])).
% 7.97/2.70  tff(c_5382, plain, (k2_relset_1(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'), '#skF_8')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_5367, c_4664])).
% 7.97/2.70  tff(c_5385, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_5367, c_4676])).
% 7.97/2.70  tff(c_5832, plain, (![C_474, B_475, A_476]: (m1_subset_1(k2_funct_1(C_474), k1_zfmisc_1(k2_zfmisc_1(B_475, A_476))) | k2_relset_1(A_476, B_475, C_474)!=B_475 | ~v2_funct_1(C_474) | ~m1_subset_1(C_474, k1_zfmisc_1(k2_zfmisc_1(A_476, B_475))) | ~v1_funct_2(C_474, A_476, B_475) | ~v1_funct_1(C_474))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.97/2.70  tff(c_54, plain, (![A_29, B_30, C_31]: (k2_relset_1(A_29, B_30, C_31)=k2_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.97/2.70  tff(c_8013, plain, (![B_588, A_589, C_590]: (k2_relset_1(B_588, A_589, k2_funct_1(C_590))=k2_relat_1(k2_funct_1(C_590)) | k2_relset_1(A_589, B_588, C_590)!=B_588 | ~v2_funct_1(C_590) | ~m1_subset_1(C_590, k1_zfmisc_1(k2_zfmisc_1(A_589, B_588))) | ~v1_funct_2(C_590, A_589, B_588) | ~v1_funct_1(C_590))), inference(resolution, [status(thm)], [c_5832, c_54])).
% 7.97/2.70  tff(c_8031, plain, (k2_relset_1(k2_relat_1('#skF_8'), k1_relat_1('#skF_8'), k2_funct_1('#skF_8'))=k2_relat_1(k2_funct_1('#skF_8')) | k2_relset_1(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'), '#skF_8')!=k2_relat_1('#skF_8') | ~v2_funct_1('#skF_8') | ~v1_funct_2('#skF_8', k1_relat_1('#skF_8'), k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_5385, c_8013])).
% 7.97/2.70  tff(c_8064, plain, (k2_relset_1(k2_relat_1('#skF_8'), k1_relat_1('#skF_8'), k2_funct_1('#skF_8'))=k2_relat_1(k2_funct_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_5387, c_92, c_5382, c_8031])).
% 7.97/2.70  tff(c_5783, plain, (![A_471, B_472, C_473]: (k2_tops_2(A_471, B_472, C_473)=k2_funct_1(C_473) | ~v2_funct_1(C_473) | k2_relset_1(A_471, B_472, C_473)!=B_472 | ~m1_subset_1(C_473, k1_zfmisc_1(k2_zfmisc_1(A_471, B_472))) | ~v1_funct_2(C_473, A_471, B_472) | ~v1_funct_1(C_473))), inference(cnfTransformation, [status(thm)], [f_184])).
% 7.97/2.70  tff(c_5786, plain, (k2_tops_2(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'), '#skF_8')=k2_funct_1('#skF_8') | ~v2_funct_1('#skF_8') | k2_relset_1(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'), '#skF_8')!=k2_relat_1('#skF_8') | ~v1_funct_2('#skF_8', k1_relat_1('#skF_8'), k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_5385, c_5783])).
% 7.97/2.70  tff(c_5809, plain, (k2_tops_2(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'), '#skF_8')=k2_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_5387, c_5382, c_92, c_5786])).
% 7.97/2.70  tff(c_349, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_200])).
% 7.97/2.70  tff(c_50, plain, (![C_25, A_23, B_24]: (v1_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.97/2.70  tff(c_359, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_349, c_50])).
% 7.97/2.70  tff(c_48, plain, (![A_22]: (k1_relat_1(k2_funct_1(A_22))=k2_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.97/2.70  tff(c_633, plain, (![A_121, B_122, C_123]: (k2_relset_1(A_121, B_122, C_123)=k2_relat_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.97/2.70  tff(c_663, plain, (k2_relset_1(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'), '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_349, c_633])).
% 7.97/2.70  tff(c_697, plain, (k2_struct_0('#skF_7')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_663, c_224])).
% 7.97/2.70  tff(c_397, plain, (![A_102]: (m1_subset_1('#skF_4'(A_102), k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_struct_0(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.97/2.70  tff(c_408, plain, (m1_subset_1('#skF_4'('#skF_7'), k1_zfmisc_1(k2_struct_0('#skF_7'))) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_198, c_397])).
% 7.97/2.70  tff(c_414, plain, (m1_subset_1('#skF_4'('#skF_7'), k1_zfmisc_1(k2_struct_0('#skF_7'))) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_408])).
% 7.97/2.70  tff(c_415, plain, (m1_subset_1('#skF_4'('#skF_7'), k1_zfmisc_1(k2_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_104, c_414])).
% 7.97/2.70  tff(c_422, plain, (v1_xboole_0('#skF_4'('#skF_7')) | ~v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_415, c_24])).
% 7.97/2.70  tff(c_424, plain, (~v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_7')))), inference(splitLeft, [status(thm)], [c_422])).
% 7.97/2.70  tff(c_299, plain, (![B_90, A_91]: (r2_hidden(B_90, A_91) | ~m1_subset_1(B_90, A_91) | v1_xboole_0(A_91))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.97/2.70  tff(c_438, plain, (![B_106, A_107]: (r1_tarski(B_106, A_107) | ~m1_subset_1(B_106, k1_zfmisc_1(A_107)) | v1_xboole_0(k1_zfmisc_1(A_107)))), inference(resolution, [status(thm)], [c_299, c_4])).
% 7.97/2.70  tff(c_441, plain, (r1_tarski('#skF_4'('#skF_7'), k2_struct_0('#skF_7')) | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_415, c_438])).
% 7.97/2.70  tff(c_464, plain, (r1_tarski('#skF_4'('#skF_7'), k2_struct_0('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_424, c_441])).
% 7.97/2.70  tff(c_478, plain, (k2_struct_0('#skF_7')!=k1_xboole_0 | '#skF_4'('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_464, c_258])).
% 7.97/2.70  tff(c_550, plain, (k2_struct_0('#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_478])).
% 7.97/2.70  tff(c_705, plain, (k2_relat_1('#skF_8')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_697, c_550])).
% 7.97/2.70  tff(c_713, plain, (v1_funct_2('#skF_8', k2_struct_0('#skF_6'), k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_697, c_213])).
% 7.97/2.70  tff(c_712, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_6'), k2_relat_1('#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_697, c_349])).
% 7.97/2.70  tff(c_52, plain, (![A_26, B_27, C_28]: (k1_relset_1(A_26, B_27, C_28)=k1_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.97/2.70  tff(c_843, plain, (k1_relset_1(k2_struct_0('#skF_6'), k2_relat_1('#skF_8'), '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_712, c_52])).
% 7.97/2.70  tff(c_1414, plain, (![B_182, A_183, C_184]: (k1_xboole_0=B_182 | k1_relset_1(A_183, B_182, C_184)=A_183 | ~v1_funct_2(C_184, A_183, B_182) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_183, B_182))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.97/2.70  tff(c_1417, plain, (k2_relat_1('#skF_8')=k1_xboole_0 | k1_relset_1(k2_struct_0('#skF_6'), k2_relat_1('#skF_8'), '#skF_8')=k2_struct_0('#skF_6') | ~v1_funct_2('#skF_8', k2_struct_0('#skF_6'), k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_712, c_1414])).
% 7.97/2.70  tff(c_1440, plain, (k2_relat_1('#skF_8')=k1_xboole_0 | k2_struct_0('#skF_6')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_713, c_843, c_1417])).
% 7.97/2.70  tff(c_1441, plain, (k2_struct_0('#skF_6')=k1_relat_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_705, c_1440])).
% 7.97/2.70  tff(c_1460, plain, (v1_funct_2('#skF_8', k1_relat_1('#skF_8'), k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1441, c_713])).
% 7.97/2.70  tff(c_702, plain, (k2_relset_1(k2_struct_0('#skF_6'), k2_relat_1('#skF_8'), '#skF_8')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_697, c_663])).
% 7.97/2.70  tff(c_1455, plain, (k2_relset_1(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'), '#skF_8')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1441, c_702])).
% 7.97/2.70  tff(c_1456, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_1441, c_712])).
% 7.97/2.70  tff(c_1864, plain, (![C_220, B_221, A_222]: (m1_subset_1(k2_funct_1(C_220), k1_zfmisc_1(k2_zfmisc_1(B_221, A_222))) | k2_relset_1(A_222, B_221, C_220)!=B_221 | ~v2_funct_1(C_220) | ~m1_subset_1(C_220, k1_zfmisc_1(k2_zfmisc_1(A_222, B_221))) | ~v1_funct_2(C_220, A_222, B_221) | ~v1_funct_1(C_220))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.97/2.70  tff(c_3791, plain, (![B_320, A_321, C_322]: (k1_relset_1(B_320, A_321, k2_funct_1(C_322))=k1_relat_1(k2_funct_1(C_322)) | k2_relset_1(A_321, B_320, C_322)!=B_320 | ~v2_funct_1(C_322) | ~m1_subset_1(C_322, k1_zfmisc_1(k2_zfmisc_1(A_321, B_320))) | ~v1_funct_2(C_322, A_321, B_320) | ~v1_funct_1(C_322))), inference(resolution, [status(thm)], [c_1864, c_52])).
% 7.97/2.70  tff(c_3809, plain, (k1_relset_1(k2_relat_1('#skF_8'), k1_relat_1('#skF_8'), k2_funct_1('#skF_8'))=k1_relat_1(k2_funct_1('#skF_8')) | k2_relset_1(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'), '#skF_8')!=k2_relat_1('#skF_8') | ~v2_funct_1('#skF_8') | ~v1_funct_2('#skF_8', k1_relat_1('#skF_8'), k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_1456, c_3791])).
% 7.97/2.70  tff(c_3842, plain, (k1_relset_1(k2_relat_1('#skF_8'), k1_relat_1('#skF_8'), k2_funct_1('#skF_8'))=k1_relat_1(k2_funct_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_1460, c_92, c_1455, c_3809])).
% 7.97/2.70  tff(c_1751, plain, (![A_209, B_210, C_211]: (k2_tops_2(A_209, B_210, C_211)=k2_funct_1(C_211) | ~v2_funct_1(C_211) | k2_relset_1(A_209, B_210, C_211)!=B_210 | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))) | ~v1_funct_2(C_211, A_209, B_210) | ~v1_funct_1(C_211))), inference(cnfTransformation, [status(thm)], [f_184])).
% 7.97/2.70  tff(c_1754, plain, (k2_tops_2(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'), '#skF_8')=k2_funct_1('#skF_8') | ~v2_funct_1('#skF_8') | k2_relset_1(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'), '#skF_8')!=k2_relat_1('#skF_8') | ~v1_funct_2('#skF_8', k1_relat_1('#skF_8'), k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_1456, c_1751])).
% 7.97/2.70  tff(c_1777, plain, (k2_tops_2(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'), '#skF_8')=k2_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_1460, c_1455, c_92, c_1754])).
% 7.97/2.70  tff(c_90, plain, (k2_relset_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_6'), k2_tops_2(u1_struct_0('#skF_6'), u1_struct_0('#skF_7'), '#skF_8'))!=k2_struct_0('#skF_6') | k1_relset_1(u1_struct_0('#skF_7'), u1_struct_0('#skF_6'), k2_tops_2(u1_struct_0('#skF_6'), u1_struct_0('#skF_7'), '#skF_8'))!=k2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_208])).
% 7.97/2.70  tff(c_271, plain, (k2_relset_1(k2_struct_0('#skF_7'), k2_struct_0('#skF_6'), k2_tops_2(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'), '#skF_8'))!=k2_struct_0('#skF_6') | k1_relset_1(k2_struct_0('#skF_7'), k2_struct_0('#skF_6'), k2_tops_2(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'), '#skF_8'))!=k2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_199, c_198, c_198, c_199, c_199, c_198, c_198, c_90])).
% 7.97/2.70  tff(c_272, plain, (k1_relset_1(k2_struct_0('#skF_7'), k2_struct_0('#skF_6'), k2_tops_2(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'), '#skF_8'))!=k2_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_271])).
% 7.97/2.70  tff(c_707, plain, (k1_relset_1(k2_relat_1('#skF_8'), k2_struct_0('#skF_6'), k2_tops_2(k2_struct_0('#skF_6'), k2_relat_1('#skF_8'), '#skF_8'))!=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_697, c_697, c_697, c_272])).
% 7.97/2.70  tff(c_1453, plain, (k1_relset_1(k2_relat_1('#skF_8'), k1_relat_1('#skF_8'), k2_tops_2(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'), '#skF_8'))!=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1441, c_1441, c_707])).
% 7.97/2.70  tff(c_1789, plain, (k1_relset_1(k2_relat_1('#skF_8'), k1_relat_1('#skF_8'), k2_funct_1('#skF_8'))!=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1777, c_1453])).
% 7.97/2.70  tff(c_3854, plain, (k1_relat_1(k2_funct_1('#skF_8'))!=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3842, c_1789])).
% 7.97/2.70  tff(c_3861, plain, (~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_48, c_3854])).
% 7.97/2.70  tff(c_3865, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_359, c_100, c_92, c_3861])).
% 7.97/2.70  tff(c_3867, plain, (k2_struct_0('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_478])).
% 7.97/2.70  tff(c_44, plain, (![C_21, B_20, A_19]: (~v1_xboole_0(C_21) | ~m1_subset_1(B_20, k1_zfmisc_1(C_21)) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.97/2.70  tff(c_421, plain, (![A_19]: (~v1_xboole_0(k2_struct_0('#skF_7')) | ~r2_hidden(A_19, '#skF_4'('#skF_7')))), inference(resolution, [status(thm)], [c_415, c_44])).
% 7.97/2.70  tff(c_423, plain, (~v1_xboole_0(k2_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_421])).
% 7.97/2.70  tff(c_3872, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3867, c_423])).
% 7.97/2.70  tff(c_3880, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_3872])).
% 7.97/2.70  tff(c_3882, plain, (v1_xboole_0(k2_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_421])).
% 7.97/2.70  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.97/2.70  tff(c_3891, plain, (k2_struct_0('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_3882, c_2])).
% 7.97/2.70  tff(c_3883, plain, (~v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_7')))), inference(splitLeft, [status(thm)], [c_422])).
% 7.97/2.70  tff(c_3924, plain, (~v1_xboole_0(k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_3891, c_3883])).
% 7.97/2.70  tff(c_3897, plain, (u1_struct_0('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3891, c_198])).
% 7.97/2.70  tff(c_80, plain, (![A_39]: (m1_subset_1('#skF_4'(A_39), k1_zfmisc_1(u1_struct_0(A_39))) | ~l1_struct_0(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.97/2.70  tff(c_3906, plain, (m1_subset_1('#skF_4'('#skF_7'), k1_zfmisc_1(k1_xboole_0)) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3897, c_80])).
% 7.97/2.70  tff(c_3910, plain, (m1_subset_1('#skF_4'('#skF_7'), k1_zfmisc_1(k1_xboole_0)) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_3906])).
% 7.97/2.70  tff(c_3911, plain, (m1_subset_1('#skF_4'('#skF_7'), k1_zfmisc_1(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_104, c_3910])).
% 7.97/2.70  tff(c_4019, plain, (![B_331, A_332]: (r1_tarski(B_331, A_332) | ~m1_subset_1(B_331, k1_zfmisc_1(A_332)) | v1_xboole_0(k1_zfmisc_1(A_332)))), inference(resolution, [status(thm)], [c_299, c_4])).
% 7.97/2.70  tff(c_4025, plain, (r1_tarski('#skF_4'('#skF_7'), k1_xboole_0) | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_3911, c_4019])).
% 7.97/2.70  tff(c_4048, plain, (r1_tarski('#skF_4'('#skF_7'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_3924, c_4025])).
% 7.97/2.70  tff(c_4059, plain, ('#skF_4'('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_4048, c_258])).
% 7.97/2.70  tff(c_22, plain, (![B_9, A_8]: (m1_subset_1(B_9, A_8) | ~v1_xboole_0(B_9) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.97/2.70  tff(c_20, plain, (![B_9, A_8]: (r2_hidden(B_9, A_8) | ~m1_subset_1(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.97/2.70  tff(c_3913, plain, (![A_323]: (~r2_hidden(A_323, '#skF_4'('#skF_7')))), inference(splitRight, [status(thm)], [c_421])).
% 7.97/2.70  tff(c_3922, plain, (![B_9]: (~m1_subset_1(B_9, '#skF_4'('#skF_7')) | v1_xboole_0('#skF_4'('#skF_7')))), inference(resolution, [status(thm)], [c_20, c_3913])).
% 7.97/2.70  tff(c_3962, plain, (![B_325]: (~m1_subset_1(B_325, '#skF_4'('#skF_7')))), inference(splitLeft, [status(thm)], [c_3922])).
% 7.97/2.70  tff(c_3973, plain, (![B_9]: (~v1_xboole_0(B_9) | ~v1_xboole_0('#skF_4'('#skF_7')))), inference(resolution, [status(thm)], [c_22, c_3962])).
% 7.97/2.70  tff(c_3974, plain, (~v1_xboole_0('#skF_4'('#skF_7'))), inference(splitLeft, [status(thm)], [c_3973])).
% 7.97/2.70  tff(c_4061, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4059, c_3974])).
% 7.97/2.70  tff(c_4069, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_4061])).
% 7.97/2.70  tff(c_4070, plain, (![B_9]: (~v1_xboole_0(B_9))), inference(splitRight, [status(thm)], [c_3973])).
% 7.97/2.70  tff(c_4078, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4070, c_142])).
% 7.97/2.70  tff(c_4079, plain, (v1_xboole_0('#skF_4'('#skF_7'))), inference(splitRight, [status(thm)], [c_3922])).
% 7.97/2.70  tff(c_78, plain, (![A_39]: (~v1_xboole_0('#skF_4'(A_39)) | ~l1_struct_0(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.97/2.70  tff(c_4085, plain, (~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_4079, c_78])).
% 7.97/2.70  tff(c_4093, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_4085])).
% 7.97/2.70  tff(c_4095, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_4093])).
% 7.97/2.70  tff(c_4096, plain, (v1_xboole_0('#skF_4'('#skF_7'))), inference(splitRight, [status(thm)], [c_422])).
% 7.97/2.70  tff(c_4120, plain, (~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_4096, c_78])).
% 7.97/2.70  tff(c_4127, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_4120])).
% 7.97/2.70  tff(c_4129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_4127])).
% 7.97/2.70  tff(c_4130, plain, (k2_relset_1(k2_struct_0('#skF_7'), k2_struct_0('#skF_6'), k2_tops_2(k2_struct_0('#skF_6'), k2_struct_0('#skF_7'), '#skF_8'))!=k2_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_271])).
% 7.97/2.70  tff(c_4675, plain, (k2_relset_1(k2_relat_1('#skF_8'), k2_struct_0('#skF_6'), k2_tops_2(k2_struct_0('#skF_6'), k2_relat_1('#skF_8'), '#skF_8'))!=k2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4659, c_4659, c_4130])).
% 7.97/2.70  tff(c_5379, plain, (k2_relset_1(k2_relat_1('#skF_8'), k1_relat_1('#skF_8'), k2_tops_2(k1_relat_1('#skF_8'), k2_relat_1('#skF_8'), '#skF_8'))!=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_5367, c_5367, c_5367, c_4675])).
% 7.97/2.70  tff(c_5822, plain, (k2_relset_1(k2_relat_1('#skF_8'), k1_relat_1('#skF_8'), k2_funct_1('#skF_8'))!=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_5809, c_5379])).
% 7.97/2.70  tff(c_8076, plain, (k2_relat_1(k2_funct_1('#skF_8'))!=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_8064, c_5822])).
% 7.97/2.70  tff(c_8083, plain, (~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_46, c_8076])).
% 7.97/2.70  tff(c_8087, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4162, c_100, c_92, c_8083])).
% 7.97/2.70  tff(c_8089, plain, (k2_struct_0('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_4378])).
% 7.97/2.70  tff(c_4282, plain, (![A_19]: (~v1_xboole_0(k2_struct_0('#skF_7')) | ~r2_hidden(A_19, '#skF_4'('#skF_7')))), inference(resolution, [status(thm)], [c_4275, c_44])).
% 7.97/2.70  tff(c_4284, plain, (~v1_xboole_0(k2_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_4282])).
% 7.97/2.70  tff(c_8094, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8089, c_4284])).
% 7.97/2.70  tff(c_8103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_8094])).
% 7.97/2.70  tff(c_8105, plain, (v1_xboole_0(k2_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_4282])).
% 7.97/2.70  tff(c_8114, plain, (k2_struct_0('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_8105, c_2])).
% 7.97/2.70  tff(c_8106, plain, (~v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_7')))), inference(splitLeft, [status(thm)], [c_4283])).
% 7.97/2.70  tff(c_8148, plain, (~v1_xboole_0(k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8114, c_8106])).
% 7.97/2.70  tff(c_8121, plain, (u1_struct_0('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8114, c_198])).
% 7.97/2.70  tff(c_8130, plain, (m1_subset_1('#skF_4'('#skF_7'), k1_zfmisc_1(k1_xboole_0)) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_8121, c_80])).
% 7.97/2.70  tff(c_8134, plain, (m1_subset_1('#skF_4'('#skF_7'), k1_zfmisc_1(k1_xboole_0)) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_8130])).
% 7.97/2.70  tff(c_8135, plain, (m1_subset_1('#skF_4'('#skF_7'), k1_zfmisc_1(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_104, c_8134])).
% 7.97/2.70  tff(c_82, plain, (![A_41, B_44]: (k3_tarski(A_41)!=k1_xboole_0 | ~r2_hidden(B_44, A_41) | k1_xboole_0=B_44)), inference(cnfTransformation, [status(thm)], [f_172])).
% 7.97/2.70  tff(c_8271, plain, (![A_602, B_603]: (k3_tarski(A_602)!=k1_xboole_0 | k1_xboole_0=B_603 | ~m1_subset_1(B_603, A_602) | v1_xboole_0(A_602))), inference(resolution, [status(thm)], [c_4167, c_82])).
% 7.97/2.70  tff(c_8280, plain, (k3_tarski(k1_zfmisc_1(k1_xboole_0))!=k1_xboole_0 | '#skF_4'('#skF_7')=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_8135, c_8271])).
% 7.97/2.70  tff(c_8303, plain, ('#skF_4'('#skF_7')=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_8280])).
% 7.97/2.70  tff(c_8304, plain, ('#skF_4'('#skF_7')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_8148, c_8303])).
% 7.97/2.70  tff(c_8137, plain, (![A_591]: (~r2_hidden(A_591, '#skF_4'('#skF_7')))), inference(splitRight, [status(thm)], [c_4282])).
% 7.97/2.70  tff(c_8146, plain, (![B_9]: (~m1_subset_1(B_9, '#skF_4'('#skF_7')) | v1_xboole_0('#skF_4'('#skF_7')))), inference(resolution, [status(thm)], [c_20, c_8137])).
% 7.97/2.70  tff(c_8192, plain, (![B_594]: (~m1_subset_1(B_594, '#skF_4'('#skF_7')))), inference(splitLeft, [status(thm)], [c_8146])).
% 7.97/2.70  tff(c_8203, plain, (![B_9]: (~v1_xboole_0(B_9) | ~v1_xboole_0('#skF_4'('#skF_7')))), inference(resolution, [status(thm)], [c_22, c_8192])).
% 7.97/2.70  tff(c_8204, plain, (~v1_xboole_0('#skF_4'('#skF_7'))), inference(splitLeft, [status(thm)], [c_8203])).
% 7.97/2.70  tff(c_8314, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8304, c_8204])).
% 7.97/2.70  tff(c_8321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_8314])).
% 7.97/2.70  tff(c_8322, plain, (![B_9]: (~v1_xboole_0(B_9))), inference(splitRight, [status(thm)], [c_8203])).
% 7.97/2.70  tff(c_8330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8322, c_142])).
% 7.97/2.70  tff(c_8331, plain, (v1_xboole_0('#skF_4'('#skF_7'))), inference(splitRight, [status(thm)], [c_8146])).
% 7.97/2.70  tff(c_8337, plain, (~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_8331, c_78])).
% 7.97/2.70  tff(c_8345, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_8337])).
% 7.97/2.70  tff(c_8347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_8345])).
% 7.97/2.70  tff(c_8348, plain, (v1_xboole_0('#skF_4'('#skF_7'))), inference(splitRight, [status(thm)], [c_4283])).
% 7.97/2.70  tff(c_8378, plain, (~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_8348, c_78])).
% 7.97/2.70  tff(c_8385, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_8378])).
% 7.97/2.70  tff(c_8387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_8385])).
% 7.97/2.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.97/2.70  
% 7.97/2.70  Inference rules
% 7.97/2.70  ----------------------
% 7.97/2.70  #Ref     : 0
% 7.97/2.70  #Sup     : 1701
% 7.97/2.70  #Fact    : 0
% 7.97/2.70  #Define  : 0
% 7.97/2.70  #Split   : 35
% 7.97/2.70  #Chain   : 0
% 7.97/2.70  #Close   : 0
% 7.97/2.70  
% 7.97/2.70  Ordering : KBO
% 7.97/2.70  
% 7.97/2.70  Simplification rules
% 7.97/2.70  ----------------------
% 7.97/2.70  #Subsume      : 494
% 7.97/2.70  #Demod        : 657
% 7.97/2.70  #Tautology    : 501
% 7.97/2.70  #SimpNegUnit  : 285
% 7.97/2.70  #BackRed      : 138
% 7.97/2.70  
% 7.97/2.70  #Partial instantiations: 0
% 7.97/2.70  #Strategies tried      : 1
% 7.97/2.70  
% 7.97/2.70  Timing (in seconds)
% 7.97/2.70  ----------------------
% 7.97/2.70  Preprocessing        : 0.38
% 7.97/2.70  Parsing              : 0.20
% 7.97/2.70  CNF conversion       : 0.03
% 7.97/2.70  Main loop            : 1.51
% 7.97/2.70  Inferencing          : 0.49
% 7.97/2.70  Reduction            : 0.49
% 7.97/2.70  Demodulation         : 0.33
% 7.97/2.70  BG Simplification    : 0.07
% 7.97/2.70  Subsumption          : 0.34
% 7.97/2.70  Abstraction          : 0.08
% 7.97/2.70  MUC search           : 0.00
% 7.97/2.70  Cooper               : 0.00
% 7.97/2.70  Total                : 1.97
% 7.97/2.71  Index Insertion      : 0.00
% 7.97/2.71  Index Deletion       : 0.00
% 7.97/2.71  Index Matching       : 0.00
% 7.97/2.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
