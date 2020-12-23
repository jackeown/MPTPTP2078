%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:18 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 194 expanded)
%              Number of leaves         :   37 (  79 expanded)
%              Depth                    :    8
%              Number of atoms          :  125 ( 395 expanded)
%              Number of equality atoms :   36 ( 106 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_132,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_30,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_142,plain,(
    ! [B_59,A_60] :
      ( v1_relat_1(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60))
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_148,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_142])).

tff(c_152,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_148])).

tff(c_224,plain,(
    ! [C_77,B_78,A_79] :
      ( v5_relat_1(C_77,B_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_233,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_224])).

tff(c_26,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_32,plain,(
    ! [A_21] :
      ( k2_relat_1(A_21) != k1_xboole_0
      | k1_xboole_0 = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_160,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_152,c_32])).

tff(c_162,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_8,plain,(
    ! [A_2,B_3] :
      ( r2_hidden('#skF_1'(A_2,B_3),B_3)
      | r1_xboole_0(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_268,plain,(
    ! [A_93,C_94,B_95] :
      ( m1_subset_1(A_93,C_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(C_94))
      | ~ r2_hidden(A_93,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_305,plain,(
    ! [A_102,B_103,A_104] :
      ( m1_subset_1(A_102,B_103)
      | ~ r2_hidden(A_102,A_104)
      | ~ r1_tarski(A_104,B_103) ) ),
    inference(resolution,[status(thm)],[c_18,c_268])).

tff(c_358,plain,(
    ! [A_120,B_121,B_122] :
      ( m1_subset_1('#skF_1'(A_120,B_121),B_122)
      | ~ r1_tarski(B_121,B_122)
      | r1_xboole_0(A_120,B_121) ) ),
    inference(resolution,[status(thm)],[c_8,c_305])).

tff(c_275,plain,(
    ! [A_96,B_97,C_98] :
      ( k2_relset_1(A_96,B_97,C_98) = k2_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_284,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_275])).

tff(c_10,plain,(
    ! [A_2,B_3] :
      ( r2_hidden('#skF_1'(A_2,B_3),A_2)
      | r1_xboole_0(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_136,plain,(
    ! [D_58] :
      ( ~ r2_hidden(D_58,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(D_58,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_141,plain,(
    ! [B_3] :
      ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4'),B_3),'#skF_3')
      | r1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4'),B_3) ) ),
    inference(resolution,[status(thm)],[c_10,c_136])).

tff(c_286,plain,(
    ! [B_3] :
      ( ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_4'),B_3),'#skF_3')
      | r1_xboole_0(k2_relat_1('#skF_4'),B_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_284,c_141])).

tff(c_403,plain,(
    ! [B_123] :
      ( ~ r1_tarski(B_123,'#skF_3')
      | r1_xboole_0(k2_relat_1('#skF_4'),B_123) ) ),
    inference(resolution,[status(thm)],[c_358,c_286])).

tff(c_14,plain,(
    ! [A_7] :
      ( ~ r1_xboole_0(A_7,A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_409,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_403,c_14])).

tff(c_413,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_409])).

tff(c_416,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_413])).

tff(c_420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_233,c_416])).

tff(c_421,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_60,plain,(
    ! [A_46] :
      ( v1_xboole_0(k1_relat_1(A_46))
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_71,plain,(
    ! [A_48] :
      ( k1_relat_1(A_48) = k1_xboole_0
      | ~ v1_xboole_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_60,c_4])).

tff(c_79,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_71])).

tff(c_433,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_421,c_79])).

tff(c_34,plain,(
    ! [A_21] :
      ( k1_relat_1(A_21) != k1_xboole_0
      | k1_xboole_0 = A_21
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_159,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_152,c_34])).

tff(c_161,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_429,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_161])).

tff(c_459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_429])).

tff(c_460,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_46,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_467,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_46])).

tff(c_465,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_460,c_79])).

tff(c_712,plain,(
    ! [A_176,B_177,C_178] :
      ( k1_relset_1(A_176,B_177,C_178) = k1_relat_1(C_178)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_719,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_712])).

tff(c_722,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_719])).

tff(c_724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_467,c_722])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 20:12:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.42  
% 2.68/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.43  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.68/1.43  
% 2.68/1.43  %Foreground sorts:
% 2.68/1.43  
% 2.68/1.43  
% 2.68/1.43  %Background operators:
% 2.68/1.43  
% 2.68/1.43  
% 2.68/1.43  %Foreground operators:
% 2.68/1.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.68/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.68/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.68/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.68/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.68/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.68/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.68/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.68/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.68/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.68/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.68/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.68/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.68/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.43  
% 2.68/1.44  tff(f_89, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.68/1.44  tff(f_132, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 2.68/1.44  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.68/1.44  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.68/1.44  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.68/1.44  tff(f_97, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.68/1.44  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.68/1.44  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.68/1.44  tff(f_70, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.68/1.44  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.68/1.44  tff(f_60, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.68/1.44  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.68/1.44  tff(f_87, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 2.68/1.44  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.68/1.44  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.68/1.44  tff(c_30, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.68/1.44  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.68/1.44  tff(c_142, plain, (![B_59, A_60]: (v1_relat_1(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.68/1.44  tff(c_148, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_142])).
% 2.68/1.44  tff(c_152, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_148])).
% 2.68/1.44  tff(c_224, plain, (![C_77, B_78, A_79]: (v5_relat_1(C_77, B_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.68/1.44  tff(c_233, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_224])).
% 2.68/1.44  tff(c_26, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(B_17), A_16) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.68/1.44  tff(c_32, plain, (![A_21]: (k2_relat_1(A_21)!=k1_xboole_0 | k1_xboole_0=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.68/1.44  tff(c_160, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_152, c_32])).
% 2.68/1.44  tff(c_162, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_160])).
% 2.68/1.44  tff(c_8, plain, (![A_2, B_3]: (r2_hidden('#skF_1'(A_2, B_3), B_3) | r1_xboole_0(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.68/1.44  tff(c_18, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.68/1.44  tff(c_268, plain, (![A_93, C_94, B_95]: (m1_subset_1(A_93, C_94) | ~m1_subset_1(B_95, k1_zfmisc_1(C_94)) | ~r2_hidden(A_93, B_95))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.68/1.44  tff(c_305, plain, (![A_102, B_103, A_104]: (m1_subset_1(A_102, B_103) | ~r2_hidden(A_102, A_104) | ~r1_tarski(A_104, B_103))), inference(resolution, [status(thm)], [c_18, c_268])).
% 2.68/1.44  tff(c_358, plain, (![A_120, B_121, B_122]: (m1_subset_1('#skF_1'(A_120, B_121), B_122) | ~r1_tarski(B_121, B_122) | r1_xboole_0(A_120, B_121))), inference(resolution, [status(thm)], [c_8, c_305])).
% 2.68/1.44  tff(c_275, plain, (![A_96, B_97, C_98]: (k2_relset_1(A_96, B_97, C_98)=k2_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.68/1.44  tff(c_284, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_275])).
% 2.68/1.44  tff(c_10, plain, (![A_2, B_3]: (r2_hidden('#skF_1'(A_2, B_3), A_2) | r1_xboole_0(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.68/1.44  tff(c_136, plain, (![D_58]: (~r2_hidden(D_58, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(D_58, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.68/1.44  tff(c_141, plain, (![B_3]: (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), B_3), '#skF_3') | r1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), B_3))), inference(resolution, [status(thm)], [c_10, c_136])).
% 2.68/1.44  tff(c_286, plain, (![B_3]: (~m1_subset_1('#skF_1'(k2_relat_1('#skF_4'), B_3), '#skF_3') | r1_xboole_0(k2_relat_1('#skF_4'), B_3))), inference(demodulation, [status(thm), theory('equality')], [c_284, c_284, c_141])).
% 2.68/1.44  tff(c_403, plain, (![B_123]: (~r1_tarski(B_123, '#skF_3') | r1_xboole_0(k2_relat_1('#skF_4'), B_123))), inference(resolution, [status(thm)], [c_358, c_286])).
% 2.68/1.44  tff(c_14, plain, (![A_7]: (~r1_xboole_0(A_7, A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.68/1.44  tff(c_409, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_403, c_14])).
% 2.68/1.44  tff(c_413, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_162, c_409])).
% 2.68/1.44  tff(c_416, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_413])).
% 2.68/1.44  tff(c_420, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_233, c_416])).
% 2.68/1.44  tff(c_421, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_160])).
% 2.68/1.44  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.68/1.44  tff(c_60, plain, (![A_46]: (v1_xboole_0(k1_relat_1(A_46)) | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.68/1.44  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.68/1.44  tff(c_71, plain, (![A_48]: (k1_relat_1(A_48)=k1_xboole_0 | ~v1_xboole_0(A_48))), inference(resolution, [status(thm)], [c_60, c_4])).
% 2.68/1.44  tff(c_79, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_71])).
% 2.68/1.44  tff(c_433, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_421, c_421, c_79])).
% 2.68/1.44  tff(c_34, plain, (![A_21]: (k1_relat_1(A_21)!=k1_xboole_0 | k1_xboole_0=A_21 | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.68/1.44  tff(c_159, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_152, c_34])).
% 2.68/1.44  tff(c_161, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_159])).
% 2.68/1.44  tff(c_429, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_421, c_161])).
% 2.68/1.44  tff(c_459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_433, c_429])).
% 2.68/1.44  tff(c_460, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_159])).
% 2.68/1.44  tff(c_46, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.68/1.44  tff(c_467, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_460, c_46])).
% 2.68/1.44  tff(c_465, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_460, c_460, c_79])).
% 2.68/1.44  tff(c_712, plain, (![A_176, B_177, C_178]: (k1_relset_1(A_176, B_177, C_178)=k1_relat_1(C_178) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.68/1.44  tff(c_719, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_712])).
% 2.68/1.44  tff(c_722, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_465, c_719])).
% 2.68/1.44  tff(c_724, plain, $false, inference(negUnitSimplification, [status(thm)], [c_467, c_722])).
% 2.68/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.44  
% 2.68/1.44  Inference rules
% 2.68/1.44  ----------------------
% 2.68/1.44  #Ref     : 0
% 2.68/1.44  #Sup     : 132
% 2.68/1.44  #Fact    : 0
% 2.68/1.44  #Define  : 0
% 2.68/1.44  #Split   : 3
% 2.68/1.44  #Chain   : 0
% 2.68/1.44  #Close   : 0
% 2.68/1.44  
% 2.68/1.44  Ordering : KBO
% 2.68/1.44  
% 2.68/1.44  Simplification rules
% 2.68/1.44  ----------------------
% 2.68/1.44  #Subsume      : 12
% 2.68/1.44  #Demod        : 85
% 2.68/1.44  #Tautology    : 59
% 2.68/1.44  #SimpNegUnit  : 2
% 2.68/1.44  #BackRed      : 28
% 2.68/1.44  
% 2.68/1.44  #Partial instantiations: 0
% 2.68/1.44  #Strategies tried      : 1
% 2.68/1.44  
% 2.68/1.44  Timing (in seconds)
% 2.68/1.44  ----------------------
% 2.68/1.44  Preprocessing        : 0.33
% 2.68/1.44  Parsing              : 0.18
% 2.68/1.44  CNF conversion       : 0.02
% 2.68/1.44  Main loop            : 0.32
% 2.68/1.45  Inferencing          : 0.12
% 2.68/1.45  Reduction            : 0.09
% 2.68/1.45  Demodulation         : 0.06
% 2.68/1.45  BG Simplification    : 0.02
% 2.68/1.45  Subsumption          : 0.05
% 2.68/1.45  Abstraction          : 0.02
% 2.68/1.45  MUC search           : 0.00
% 2.68/1.45  Cooper               : 0.00
% 2.68/1.45  Total                : 0.68
% 2.68/1.45  Index Insertion      : 0.00
% 2.68/1.45  Index Deletion       : 0.00
% 2.68/1.45  Index Matching       : 0.00
% 2.68/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
