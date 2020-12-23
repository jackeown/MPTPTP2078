%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:40 EST 2020

% Result     : Theorem 8.67s
% Output     : CNFRefutation 8.93s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 658 expanded)
%              Number of leaves         :   43 ( 239 expanded)
%              Depth                    :   16
%              Number of atoms          :  261 (1744 expanded)
%              Number of equality atoms :   71 ( 258 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( r2_hidden(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_125,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_143,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_80,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_962,plain,(
    ! [A_187,B_188,D_189] :
      ( r2_relset_1(A_187,B_188,D_189,D_189)
      | ~ m1_subset_1(D_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_978,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_962])).

tff(c_32,plain,(
    ! [A_21,B_22] : v1_relat_1(k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_74,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_183,plain,(
    ! [B_79,A_80] :
      ( v1_relat_1(B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_80))
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_189,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_74,c_183])).

tff(c_198,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_189])).

tff(c_78,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_733,plain,(
    ! [C_160,B_161,A_162] :
      ( v1_xboole_0(C_160)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(B_161,A_162)))
      | ~ v1_xboole_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_750,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_733])).

tff(c_756,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_750])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_76,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_2456,plain,(
    ! [A_299,B_300,C_301] :
      ( k1_relset_1(A_299,B_300,C_301) = k1_relat_1(C_301)
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(A_299,B_300))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2479,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_2456])).

tff(c_4631,plain,(
    ! [B_458,A_459,C_460] :
      ( k1_xboole_0 = B_458
      | k1_relset_1(A_459,B_458,C_460) = A_459
      | ~ v1_funct_2(C_460,A_459,B_458)
      | ~ m1_subset_1(C_460,k1_zfmisc_1(k2_zfmisc_1(A_459,B_458))) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_4637,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_4631])).

tff(c_4653,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2479,c_4637])).

tff(c_4657,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4653])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_637,plain,(
    ! [C_146,A_147,B_148] :
      ( v4_relat_1(C_146,A_147)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_655,plain,(
    v4_relat_1('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_637])).

tff(c_34,plain,(
    ! [B_24,A_23] :
      ( k7_relat_1(B_24,A_23) = B_24
      | ~ v4_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_672,plain,
    ( k7_relat_1('#skF_7','#skF_4') = '#skF_7'
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_655,c_34])).

tff(c_675,plain,(
    k7_relat_1('#skF_7','#skF_4') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_672])).

tff(c_820,plain,(
    ! [A_172,B_173,C_174] :
      ( r2_hidden(A_172,B_173)
      | ~ r2_hidden(A_172,k1_relat_1(k7_relat_1(C_174,B_173)))
      | ~ v1_relat_1(C_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_830,plain,(
    ! [A_172] :
      ( r2_hidden(A_172,'#skF_4')
      | ~ r2_hidden(A_172,k1_relat_1('#skF_7'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_675,c_820])).

tff(c_864,plain,(
    ! [A_177] :
      ( r2_hidden(A_177,'#skF_4')
      | ~ r2_hidden(A_177,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_830])).

tff(c_4562,plain,(
    ! [B_453] :
      ( r2_hidden('#skF_2'(k1_relat_1('#skF_7'),B_453),'#skF_4')
      | r1_tarski(k1_relat_1('#skF_7'),B_453) ) ),
    inference(resolution,[status(thm)],[c_10,c_864])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4576,plain,(
    r1_tarski(k1_relat_1('#skF_7'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_4562,c_8])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4599,plain,
    ( k1_relat_1('#skF_7') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_4576,c_14])).

tff(c_4600,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_4599])).

tff(c_4659,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4657,c_4600])).

tff(c_4671,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4659])).

tff(c_4672,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4653])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4707,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4672,c_12])).

tff(c_4709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_756,c_4707])).

tff(c_4710,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4599])).

tff(c_186,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_80,c_183])).

tff(c_195,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_186])).

tff(c_84,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_82,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_2478,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_2456])).

tff(c_3973,plain,(
    ! [B_408,A_409,C_410] :
      ( k1_xboole_0 = B_408
      | k1_relset_1(A_409,B_408,C_410) = A_409
      | ~ v1_funct_2(C_410,A_409,B_408)
      | ~ m1_subset_1(C_410,k1_zfmisc_1(k2_zfmisc_1(A_409,B_408))) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3976,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_3973])).

tff(c_3992,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2478,c_3976])).

tff(c_4003,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3992])).

tff(c_654,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_637])).

tff(c_659,plain,
    ( k7_relat_1('#skF_6','#skF_4') = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_654,c_34])).

tff(c_662,plain,(
    k7_relat_1('#skF_6','#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_659])).

tff(c_833,plain,(
    ! [A_172] :
      ( r2_hidden(A_172,'#skF_4')
      | ~ r2_hidden(A_172,k1_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_820])).

tff(c_880,plain,(
    ! [A_178] :
      ( r2_hidden(A_178,'#skF_4')
      | ~ r2_hidden(A_178,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_833])).

tff(c_3460,plain,(
    ! [B_367] :
      ( r2_hidden('#skF_2'(k1_relat_1('#skF_6'),B_367),'#skF_4')
      | r1_tarski(k1_relat_1('#skF_6'),B_367) ) ),
    inference(resolution,[status(thm)],[c_10,c_880])).

tff(c_3474,plain,(
    r1_tarski(k1_relat_1('#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_3460,c_8])).

tff(c_3488,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_3474,c_14])).

tff(c_3489,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_3488])).

tff(c_4005,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4003,c_3489])).

tff(c_4016,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4005])).

tff(c_4017,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3992])).

tff(c_4071,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4017,c_12])).

tff(c_4073,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_756,c_4071])).

tff(c_4074,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3488])).

tff(c_5056,plain,(
    ! [A_502,B_503] :
      ( r2_hidden('#skF_3'(A_502,B_503),k1_relat_1(A_502))
      | B_503 = A_502
      | k1_relat_1(B_503) != k1_relat_1(A_502)
      | ~ v1_funct_1(B_503)
      | ~ v1_relat_1(B_503)
      | ~ v1_funct_1(A_502)
      | ~ v1_relat_1(A_502) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_40,plain,(
    ! [A_25,B_26,C_27] :
      ( r2_hidden(A_25,B_26)
      | ~ r2_hidden(A_25,k1_relat_1(k7_relat_1(C_27,B_26)))
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_8088,plain,(
    ! [C_609,B_610,B_611] :
      ( r2_hidden('#skF_3'(k7_relat_1(C_609,B_610),B_611),B_610)
      | ~ v1_relat_1(C_609)
      | k7_relat_1(C_609,B_610) = B_611
      | k1_relat_1(k7_relat_1(C_609,B_610)) != k1_relat_1(B_611)
      | ~ v1_funct_1(B_611)
      | ~ v1_relat_1(B_611)
      | ~ v1_funct_1(k7_relat_1(C_609,B_610))
      | ~ v1_relat_1(k7_relat_1(C_609,B_610)) ) ),
    inference(resolution,[status(thm)],[c_5056,c_40])).

tff(c_8123,plain,(
    ! [B_611] :
      ( r2_hidden('#skF_3'('#skF_6',B_611),'#skF_4')
      | ~ v1_relat_1('#skF_6')
      | k7_relat_1('#skF_6','#skF_4') = B_611
      | k1_relat_1(k7_relat_1('#skF_6','#skF_4')) != k1_relat_1(B_611)
      | ~ v1_funct_1(B_611)
      | ~ v1_relat_1(B_611)
      | ~ v1_funct_1(k7_relat_1('#skF_6','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_6','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_8088])).

tff(c_8864,plain,(
    ! [B_637] :
      ( r2_hidden('#skF_3'('#skF_6',B_637),'#skF_4')
      | B_637 = '#skF_6'
      | k1_relat_1(B_637) != '#skF_4'
      | ~ v1_funct_1(B_637)
      | ~ v1_relat_1(B_637) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_662,c_84,c_662,c_4074,c_662,c_662,c_195,c_8123])).

tff(c_72,plain,(
    ! [E_55] :
      ( k1_funct_1('#skF_7',E_55) = k1_funct_1('#skF_6',E_55)
      | ~ r2_hidden(E_55,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_10838,plain,(
    ! [B_679] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_6',B_679)) = k1_funct_1('#skF_6','#skF_3'('#skF_6',B_679))
      | B_679 = '#skF_6'
      | k1_relat_1(B_679) != '#skF_4'
      | ~ v1_funct_1(B_679)
      | ~ v1_relat_1(B_679) ) ),
    inference(resolution,[status(thm)],[c_8864,c_72])).

tff(c_42,plain,(
    ! [B_32,A_28] :
      ( k1_funct_1(B_32,'#skF_3'(A_28,B_32)) != k1_funct_1(A_28,'#skF_3'(A_28,B_32))
      | B_32 = A_28
      | k1_relat_1(B_32) != k1_relat_1(A_28)
      | ~ v1_funct_1(B_32)
      | ~ v1_relat_1(B_32)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_10845,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_10838,c_42])).

tff(c_10852,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_78,c_4710,c_195,c_84,c_4710,c_4074,c_10845])).

tff(c_70,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_10898,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10852,c_70])).

tff(c_10913,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_978,c_10898])).

tff(c_10914,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_750])).

tff(c_153,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_2'(A_73,B_74),A_73)
      | r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_168,plain,(
    ! [A_73,B_74] :
      ( ~ v1_xboole_0(A_73)
      | r1_tarski(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_153,c_2])).

tff(c_169,plain,(
    ! [A_75,B_76] :
      ( ~ v1_xboole_0(A_75)
      | r1_tarski(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_153,c_2])).

tff(c_173,plain,(
    ! [B_77,A_78] :
      ( B_77 = A_78
      | ~ r1_tarski(B_77,A_78)
      | ~ v1_xboole_0(A_78) ) ),
    inference(resolution,[status(thm)],[c_169,c_14])).

tff(c_201,plain,(
    ! [B_81,A_82] :
      ( B_81 = A_82
      | ~ v1_xboole_0(B_81)
      | ~ v1_xboole_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_168,c_173])).

tff(c_204,plain,(
    ! [A_82] :
      ( k1_xboole_0 = A_82
      | ~ v1_xboole_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_12,c_201])).

tff(c_10921,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_10914,c_204])).

tff(c_26,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_11033,plain,(
    ! [A_690] : m1_subset_1('#skF_6',k1_zfmisc_1(A_690)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10921,c_26])).

tff(c_54,plain,(
    ! [A_44,B_45,D_47] :
      ( r2_relset_1(A_44,B_45,D_47,D_47)
      | ~ m1_subset_1(D_47,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_11054,plain,(
    ! [A_44,B_45] : r2_relset_1(A_44,B_45,'#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_11033,c_54])).

tff(c_10915,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_750])).

tff(c_10928,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_10915,c_204])).

tff(c_10949,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10921,c_10928])).

tff(c_751,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_733])).

tff(c_10975,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10914,c_10949,c_751])).

tff(c_180,plain,(
    ! [B_74,A_73] :
      ( B_74 = A_73
      | ~ v1_xboole_0(B_74)
      | ~ v1_xboole_0(A_73) ) ),
    inference(resolution,[status(thm)],[c_168,c_173])).

tff(c_10979,plain,(
    ! [A_685] :
      ( A_685 = '#skF_6'
      | ~ v1_xboole_0(A_685) ) ),
    inference(resolution,[status(thm)],[c_10914,c_180])).

tff(c_10986,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_10975,c_10979])).

tff(c_10955,plain,(
    ~ r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10949,c_70])).

tff(c_11104,plain,(
    ~ r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10986,c_10955])).

tff(c_11128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11054,c_11104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.67/3.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.67/3.05  
% 8.67/3.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.67/3.05  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 8.67/3.05  
% 8.67/3.05  %Foreground sorts:
% 8.67/3.05  
% 8.67/3.05  
% 8.67/3.05  %Background operators:
% 8.67/3.05  
% 8.67/3.05  
% 8.67/3.05  %Foreground operators:
% 8.67/3.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.67/3.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.67/3.05  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.67/3.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.67/3.05  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.67/3.05  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.67/3.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.67/3.05  tff('#skF_7', type, '#skF_7': $i).
% 8.67/3.05  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.67/3.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.67/3.05  tff('#skF_5', type, '#skF_5': $i).
% 8.67/3.05  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.67/3.05  tff('#skF_6', type, '#skF_6': $i).
% 8.67/3.05  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.67/3.05  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.67/3.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.67/3.05  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.67/3.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.67/3.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.67/3.05  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.67/3.05  tff('#skF_4', type, '#skF_4': $i).
% 8.67/3.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.67/3.05  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.67/3.05  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.67/3.05  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.67/3.05  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.67/3.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.67/3.05  
% 8.93/3.07  tff(f_164, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 8.93/3.07  tff(f_125, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.93/3.07  tff(f_68, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.93/3.07  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.93/3.07  tff(f_113, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 8.93/3.07  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.93/3.07  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.93/3.07  tff(f_143, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 8.93/3.07  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 8.93/3.07  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.93/3.07  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 8.93/3.07  tff(f_82, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 8.93/3.07  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.93/3.07  tff(f_100, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 8.93/3.07  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.93/3.07  tff(f_53, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 8.93/3.07  tff(c_80, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 8.93/3.07  tff(c_962, plain, (![A_187, B_188, D_189]: (r2_relset_1(A_187, B_188, D_189, D_189) | ~m1_subset_1(D_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.93/3.07  tff(c_978, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_80, c_962])).
% 8.93/3.07  tff(c_32, plain, (![A_21, B_22]: (v1_relat_1(k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.93/3.07  tff(c_74, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 8.93/3.07  tff(c_183, plain, (![B_79, A_80]: (v1_relat_1(B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(A_80)) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.93/3.07  tff(c_189, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_74, c_183])).
% 8.93/3.07  tff(c_198, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_189])).
% 8.93/3.07  tff(c_78, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_164])).
% 8.93/3.07  tff(c_733, plain, (![C_160, B_161, A_162]: (v1_xboole_0(C_160) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(B_161, A_162))) | ~v1_xboole_0(A_162))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.93/3.07  tff(c_750, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_80, c_733])).
% 8.93/3.07  tff(c_756, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_750])).
% 8.93/3.07  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.93/3.07  tff(c_76, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_164])).
% 8.93/3.07  tff(c_2456, plain, (![A_299, B_300, C_301]: (k1_relset_1(A_299, B_300, C_301)=k1_relat_1(C_301) | ~m1_subset_1(C_301, k1_zfmisc_1(k2_zfmisc_1(A_299, B_300))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.93/3.07  tff(c_2479, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_74, c_2456])).
% 8.93/3.07  tff(c_4631, plain, (![B_458, A_459, C_460]: (k1_xboole_0=B_458 | k1_relset_1(A_459, B_458, C_460)=A_459 | ~v1_funct_2(C_460, A_459, B_458) | ~m1_subset_1(C_460, k1_zfmisc_1(k2_zfmisc_1(A_459, B_458))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.93/3.07  tff(c_4637, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_74, c_4631])).
% 8.93/3.07  tff(c_4653, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2479, c_4637])).
% 8.93/3.07  tff(c_4657, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_4653])).
% 8.93/3.07  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.93/3.07  tff(c_637, plain, (![C_146, A_147, B_148]: (v4_relat_1(C_146, A_147) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.93/3.07  tff(c_655, plain, (v4_relat_1('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_637])).
% 8.93/3.07  tff(c_34, plain, (![B_24, A_23]: (k7_relat_1(B_24, A_23)=B_24 | ~v4_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.93/3.07  tff(c_672, plain, (k7_relat_1('#skF_7', '#skF_4')='#skF_7' | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_655, c_34])).
% 8.93/3.07  tff(c_675, plain, (k7_relat_1('#skF_7', '#skF_4')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_198, c_672])).
% 8.93/3.07  tff(c_820, plain, (![A_172, B_173, C_174]: (r2_hidden(A_172, B_173) | ~r2_hidden(A_172, k1_relat_1(k7_relat_1(C_174, B_173))) | ~v1_relat_1(C_174))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.93/3.07  tff(c_830, plain, (![A_172]: (r2_hidden(A_172, '#skF_4') | ~r2_hidden(A_172, k1_relat_1('#skF_7')) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_675, c_820])).
% 8.93/3.07  tff(c_864, plain, (![A_177]: (r2_hidden(A_177, '#skF_4') | ~r2_hidden(A_177, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_830])).
% 8.93/3.07  tff(c_4562, plain, (![B_453]: (r2_hidden('#skF_2'(k1_relat_1('#skF_7'), B_453), '#skF_4') | r1_tarski(k1_relat_1('#skF_7'), B_453))), inference(resolution, [status(thm)], [c_10, c_864])).
% 8.93/3.07  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.93/3.07  tff(c_4576, plain, (r1_tarski(k1_relat_1('#skF_7'), '#skF_4')), inference(resolution, [status(thm)], [c_4562, c_8])).
% 8.93/3.07  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.93/3.07  tff(c_4599, plain, (k1_relat_1('#skF_7')='#skF_4' | ~r1_tarski('#skF_4', k1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_4576, c_14])).
% 8.93/3.07  tff(c_4600, plain, (~r1_tarski('#skF_4', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_4599])).
% 8.93/3.07  tff(c_4659, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4657, c_4600])).
% 8.93/3.07  tff(c_4671, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_4659])).
% 8.93/3.07  tff(c_4672, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_4653])).
% 8.93/3.07  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.93/3.07  tff(c_4707, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4672, c_12])).
% 8.93/3.07  tff(c_4709, plain, $false, inference(negUnitSimplification, [status(thm)], [c_756, c_4707])).
% 8.93/3.07  tff(c_4710, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitRight, [status(thm)], [c_4599])).
% 8.93/3.07  tff(c_186, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_80, c_183])).
% 8.93/3.07  tff(c_195, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_186])).
% 8.93/3.07  tff(c_84, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_164])).
% 8.93/3.07  tff(c_82, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_164])).
% 8.93/3.07  tff(c_2478, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_2456])).
% 8.93/3.07  tff(c_3973, plain, (![B_408, A_409, C_410]: (k1_xboole_0=B_408 | k1_relset_1(A_409, B_408, C_410)=A_409 | ~v1_funct_2(C_410, A_409, B_408) | ~m1_subset_1(C_410, k1_zfmisc_1(k2_zfmisc_1(A_409, B_408))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.93/3.07  tff(c_3976, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_80, c_3973])).
% 8.93/3.07  tff(c_3992, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2478, c_3976])).
% 8.93/3.07  tff(c_4003, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_3992])).
% 8.93/3.07  tff(c_654, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_80, c_637])).
% 8.93/3.07  tff(c_659, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_654, c_34])).
% 8.93/3.07  tff(c_662, plain, (k7_relat_1('#skF_6', '#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_195, c_659])).
% 8.93/3.07  tff(c_833, plain, (![A_172]: (r2_hidden(A_172, '#skF_4') | ~r2_hidden(A_172, k1_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_662, c_820])).
% 8.93/3.07  tff(c_880, plain, (![A_178]: (r2_hidden(A_178, '#skF_4') | ~r2_hidden(A_178, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_833])).
% 8.93/3.07  tff(c_3460, plain, (![B_367]: (r2_hidden('#skF_2'(k1_relat_1('#skF_6'), B_367), '#skF_4') | r1_tarski(k1_relat_1('#skF_6'), B_367))), inference(resolution, [status(thm)], [c_10, c_880])).
% 8.93/3.07  tff(c_3474, plain, (r1_tarski(k1_relat_1('#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_3460, c_8])).
% 8.93/3.07  tff(c_3488, plain, (k1_relat_1('#skF_6')='#skF_4' | ~r1_tarski('#skF_4', k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_3474, c_14])).
% 8.93/3.07  tff(c_3489, plain, (~r1_tarski('#skF_4', k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_3488])).
% 8.93/3.07  tff(c_4005, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4003, c_3489])).
% 8.93/3.07  tff(c_4016, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_4005])).
% 8.93/3.07  tff(c_4017, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_3992])).
% 8.93/3.07  tff(c_4071, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4017, c_12])).
% 8.93/3.07  tff(c_4073, plain, $false, inference(negUnitSimplification, [status(thm)], [c_756, c_4071])).
% 8.93/3.07  tff(c_4074, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_3488])).
% 8.93/3.07  tff(c_5056, plain, (![A_502, B_503]: (r2_hidden('#skF_3'(A_502, B_503), k1_relat_1(A_502)) | B_503=A_502 | k1_relat_1(B_503)!=k1_relat_1(A_502) | ~v1_funct_1(B_503) | ~v1_relat_1(B_503) | ~v1_funct_1(A_502) | ~v1_relat_1(A_502))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.93/3.07  tff(c_40, plain, (![A_25, B_26, C_27]: (r2_hidden(A_25, B_26) | ~r2_hidden(A_25, k1_relat_1(k7_relat_1(C_27, B_26))) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.93/3.07  tff(c_8088, plain, (![C_609, B_610, B_611]: (r2_hidden('#skF_3'(k7_relat_1(C_609, B_610), B_611), B_610) | ~v1_relat_1(C_609) | k7_relat_1(C_609, B_610)=B_611 | k1_relat_1(k7_relat_1(C_609, B_610))!=k1_relat_1(B_611) | ~v1_funct_1(B_611) | ~v1_relat_1(B_611) | ~v1_funct_1(k7_relat_1(C_609, B_610)) | ~v1_relat_1(k7_relat_1(C_609, B_610)))), inference(resolution, [status(thm)], [c_5056, c_40])).
% 8.93/3.07  tff(c_8123, plain, (![B_611]: (r2_hidden('#skF_3'('#skF_6', B_611), '#skF_4') | ~v1_relat_1('#skF_6') | k7_relat_1('#skF_6', '#skF_4')=B_611 | k1_relat_1(k7_relat_1('#skF_6', '#skF_4'))!=k1_relat_1(B_611) | ~v1_funct_1(B_611) | ~v1_relat_1(B_611) | ~v1_funct_1(k7_relat_1('#skF_6', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_6', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_662, c_8088])).
% 8.93/3.07  tff(c_8864, plain, (![B_637]: (r2_hidden('#skF_3'('#skF_6', B_637), '#skF_4') | B_637='#skF_6' | k1_relat_1(B_637)!='#skF_4' | ~v1_funct_1(B_637) | ~v1_relat_1(B_637))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_662, c_84, c_662, c_4074, c_662, c_662, c_195, c_8123])).
% 8.93/3.07  tff(c_72, plain, (![E_55]: (k1_funct_1('#skF_7', E_55)=k1_funct_1('#skF_6', E_55) | ~r2_hidden(E_55, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 8.93/3.07  tff(c_10838, plain, (![B_679]: (k1_funct_1('#skF_7', '#skF_3'('#skF_6', B_679))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_679)) | B_679='#skF_6' | k1_relat_1(B_679)!='#skF_4' | ~v1_funct_1(B_679) | ~v1_relat_1(B_679))), inference(resolution, [status(thm)], [c_8864, c_72])).
% 8.93/3.07  tff(c_42, plain, (![B_32, A_28]: (k1_funct_1(B_32, '#skF_3'(A_28, B_32))!=k1_funct_1(A_28, '#skF_3'(A_28, B_32)) | B_32=A_28 | k1_relat_1(B_32)!=k1_relat_1(A_28) | ~v1_funct_1(B_32) | ~v1_relat_1(B_32) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.93/3.07  tff(c_10845, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_10838, c_42])).
% 8.93/3.07  tff(c_10852, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_198, c_78, c_4710, c_195, c_84, c_4710, c_4074, c_10845])).
% 8.93/3.07  tff(c_70, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_164])).
% 8.93/3.07  tff(c_10898, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10852, c_70])).
% 8.93/3.07  tff(c_10913, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_978, c_10898])).
% 8.93/3.07  tff(c_10914, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_750])).
% 8.93/3.07  tff(c_153, plain, (![A_73, B_74]: (r2_hidden('#skF_2'(A_73, B_74), A_73) | r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.93/3.07  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.93/3.07  tff(c_168, plain, (![A_73, B_74]: (~v1_xboole_0(A_73) | r1_tarski(A_73, B_74))), inference(resolution, [status(thm)], [c_153, c_2])).
% 8.93/3.07  tff(c_169, plain, (![A_75, B_76]: (~v1_xboole_0(A_75) | r1_tarski(A_75, B_76))), inference(resolution, [status(thm)], [c_153, c_2])).
% 8.93/3.07  tff(c_173, plain, (![B_77, A_78]: (B_77=A_78 | ~r1_tarski(B_77, A_78) | ~v1_xboole_0(A_78))), inference(resolution, [status(thm)], [c_169, c_14])).
% 8.93/3.07  tff(c_201, plain, (![B_81, A_82]: (B_81=A_82 | ~v1_xboole_0(B_81) | ~v1_xboole_0(A_82))), inference(resolution, [status(thm)], [c_168, c_173])).
% 8.93/3.07  tff(c_204, plain, (![A_82]: (k1_xboole_0=A_82 | ~v1_xboole_0(A_82))), inference(resolution, [status(thm)], [c_12, c_201])).
% 8.93/3.07  tff(c_10921, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_10914, c_204])).
% 8.93/3.07  tff(c_26, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.93/3.07  tff(c_11033, plain, (![A_690]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_690)))), inference(demodulation, [status(thm), theory('equality')], [c_10921, c_26])).
% 8.93/3.07  tff(c_54, plain, (![A_44, B_45, D_47]: (r2_relset_1(A_44, B_45, D_47, D_47) | ~m1_subset_1(D_47, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.93/3.07  tff(c_11054, plain, (![A_44, B_45]: (r2_relset_1(A_44, B_45, '#skF_6', '#skF_6'))), inference(resolution, [status(thm)], [c_11033, c_54])).
% 8.93/3.07  tff(c_10915, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_750])).
% 8.93/3.07  tff(c_10928, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_10915, c_204])).
% 8.93/3.07  tff(c_10949, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10921, c_10928])).
% 8.93/3.07  tff(c_751, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_74, c_733])).
% 8.93/3.07  tff(c_10975, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_10914, c_10949, c_751])).
% 8.93/3.07  tff(c_180, plain, (![B_74, A_73]: (B_74=A_73 | ~v1_xboole_0(B_74) | ~v1_xboole_0(A_73))), inference(resolution, [status(thm)], [c_168, c_173])).
% 8.93/3.07  tff(c_10979, plain, (![A_685]: (A_685='#skF_6' | ~v1_xboole_0(A_685))), inference(resolution, [status(thm)], [c_10914, c_180])).
% 8.93/3.07  tff(c_10986, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_10975, c_10979])).
% 8.93/3.07  tff(c_10955, plain, (~r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_10949, c_70])).
% 8.93/3.07  tff(c_11104, plain, (~r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10986, c_10955])).
% 8.93/3.07  tff(c_11128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11054, c_11104])).
% 8.93/3.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.93/3.07  
% 8.93/3.07  Inference rules
% 8.93/3.07  ----------------------
% 8.93/3.07  #Ref     : 1
% 8.93/3.07  #Sup     : 2333
% 8.93/3.07  #Fact    : 0
% 8.93/3.07  #Define  : 0
% 8.93/3.07  #Split   : 36
% 8.93/3.07  #Chain   : 0
% 8.93/3.07  #Close   : 0
% 8.93/3.07  
% 8.93/3.07  Ordering : KBO
% 8.93/3.07  
% 8.93/3.07  Simplification rules
% 8.93/3.07  ----------------------
% 8.93/3.07  #Subsume      : 960
% 8.93/3.07  #Demod        : 2609
% 8.93/3.07  #Tautology    : 834
% 8.93/3.07  #SimpNegUnit  : 135
% 8.93/3.07  #BackRed      : 574
% 8.93/3.07  
% 8.93/3.07  #Partial instantiations: 0
% 8.93/3.07  #Strategies tried      : 1
% 8.93/3.07  
% 8.93/3.07  Timing (in seconds)
% 8.93/3.07  ----------------------
% 8.93/3.07  Preprocessing        : 0.37
% 8.93/3.07  Parsing              : 0.19
% 8.93/3.07  CNF conversion       : 0.03
% 8.93/3.07  Main loop            : 1.93
% 8.93/3.07  Inferencing          : 0.57
% 8.93/3.07  Reduction            : 0.66
% 8.93/3.07  Demodulation         : 0.47
% 8.93/3.07  BG Simplification    : 0.07
% 8.93/3.07  Subsumption          : 0.47
% 8.93/3.07  Abstraction          : 0.08
% 8.93/3.07  MUC search           : 0.00
% 8.93/3.07  Cooper               : 0.00
% 8.93/3.07  Total                : 2.34
% 8.93/3.07  Index Insertion      : 0.00
% 8.93/3.07  Index Deletion       : 0.00
% 8.93/3.07  Index Matching       : 0.00
% 8.93/3.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
