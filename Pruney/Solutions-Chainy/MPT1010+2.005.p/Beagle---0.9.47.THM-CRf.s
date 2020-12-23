%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:05 EST 2020

% Result     : Theorem 5.86s
% Output     : CNFRefutation 6.19s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 109 expanded)
%              Number of leaves         :   45 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  126 ( 208 expanded)
%              Number of equality atoms :   27 (  54 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_136,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_125,axiom,(
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

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_58,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_93,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_84,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_88,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_281,plain,(
    ! [C_112,B_113,A_114] :
      ( v5_relat_1(C_112,B_113)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_114,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_290,plain,(
    v5_relat_1('#skF_8',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_88,c_281])).

tff(c_86,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_216,plain,(
    ! [C_91,A_92,B_93] :
      ( v1_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_225,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_88,c_216])).

tff(c_92,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_90,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_868,plain,(
    ! [A_2130,B_2131,C_2132] :
      ( k1_relset_1(A_2130,B_2131,C_2132) = k1_relat_1(C_2132)
      | ~ m1_subset_1(C_2132,k1_zfmisc_1(k2_zfmisc_1(A_2130,B_2131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_879,plain,(
    k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_88,c_868])).

tff(c_1986,plain,(
    ! [B_4454,A_4455,C_4456] :
      ( k1_xboole_0 = B_4454
      | k1_relset_1(A_4455,B_4454,C_4456) = A_4455
      | ~ v1_funct_2(C_4456,A_4455,B_4454)
      | ~ m1_subset_1(C_4456,k1_zfmisc_1(k2_zfmisc_1(A_4455,B_4454))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1995,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_88,c_1986])).

tff(c_1999,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_879,c_1995])).

tff(c_2000,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1999])).

tff(c_58,plain,(
    ! [B_29,A_28] :
      ( r1_tarski(k2_relat_1(B_29),A_28)
      | ~ v5_relat_1(B_29,A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1560,plain,(
    ! [B_3921,A_3922] :
      ( r2_hidden(k1_funct_1(B_3921,A_3922),k2_relat_1(B_3921))
      | ~ r2_hidden(A_3922,k1_relat_1(B_3921))
      | ~ v1_funct_1(B_3921)
      | ~ v1_relat_1(B_3921) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_52,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(A_23,k1_zfmisc_1(B_24))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_327,plain,(
    ! [A_121,C_122,B_123] :
      ( m1_subset_1(A_121,C_122)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(C_122))
      | ~ r2_hidden(A_121,B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_332,plain,(
    ! [A_121,B_24,A_23] :
      ( m1_subset_1(A_121,B_24)
      | ~ r2_hidden(A_121,A_23)
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_52,c_327])).

tff(c_4857,plain,(
    ! [B_7712,A_7713,B_7714] :
      ( m1_subset_1(k1_funct_1(B_7712,A_7713),B_7714)
      | ~ r1_tarski(k2_relat_1(B_7712),B_7714)
      | ~ r2_hidden(A_7713,k1_relat_1(B_7712))
      | ~ v1_funct_1(B_7712)
      | ~ v1_relat_1(B_7712) ) ),
    inference(resolution,[status(thm)],[c_1560,c_332])).

tff(c_4862,plain,(
    ! [B_7747,A_7748,A_7749] :
      ( m1_subset_1(k1_funct_1(B_7747,A_7748),A_7749)
      | ~ r2_hidden(A_7748,k1_relat_1(B_7747))
      | ~ v1_funct_1(B_7747)
      | ~ v5_relat_1(B_7747,A_7749)
      | ~ v1_relat_1(B_7747) ) ),
    inference(resolution,[status(thm)],[c_58,c_4857])).

tff(c_4876,plain,(
    ! [A_7748,A_7749] :
      ( m1_subset_1(k1_funct_1('#skF_8',A_7748),A_7749)
      | ~ r2_hidden(A_7748,'#skF_5')
      | ~ v1_funct_1('#skF_8')
      | ~ v5_relat_1('#skF_8',A_7749)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2000,c_4862])).

tff(c_4892,plain,(
    ! [A_7782,A_7783] :
      ( m1_subset_1(k1_funct_1('#skF_8',A_7782),A_7783)
      | ~ r2_hidden(A_7782,'#skF_5')
      | ~ v5_relat_1('#skF_8',A_7783) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_92,c_4876])).

tff(c_46,plain,(
    ! [A_20] : ~ v1_xboole_0(k1_tarski(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_203,plain,(
    ! [A_87,B_88] :
      ( r2_hidden(A_87,B_88)
      | v1_xboole_0(B_88)
      | ~ m1_subset_1(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_207,plain,(
    ! [A_9,A_87] :
      ( A_9 = A_87
      | v1_xboole_0(k1_tarski(A_9))
      | ~ m1_subset_1(A_87,k1_tarski(A_9)) ) ),
    inference(resolution,[status(thm)],[c_203,c_28])).

tff(c_213,plain,(
    ! [A_9,A_87] :
      ( A_9 = A_87
      | ~ m1_subset_1(A_87,k1_tarski(A_9)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_207])).

tff(c_4985,plain,(
    ! [A_7848,A_7849] :
      ( k1_funct_1('#skF_8',A_7848) = A_7849
      | ~ r2_hidden(A_7848,'#skF_5')
      | ~ v5_relat_1('#skF_8',k1_tarski(A_7849)) ) ),
    inference(resolution,[status(thm)],[c_4892,c_213])).

tff(c_5019,plain,(
    ! [A_7882] :
      ( k1_funct_1('#skF_8','#skF_7') = A_7882
      | ~ v5_relat_1('#skF_8',k1_tarski(A_7882)) ) ),
    inference(resolution,[status(thm)],[c_86,c_4985])).

tff(c_5026,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_290,c_5019])).

tff(c_5030,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_5026])).

tff(c_5031,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1999])).

tff(c_30,plain,(
    ! [C_13] : r2_hidden(C_13,k1_tarski(C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_108,plain,(
    ! [B_59,A_60] :
      ( ~ r1_tarski(B_59,A_60)
      | ~ r2_hidden(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_127,plain,(
    ! [C_13] : ~ r1_tarski(k1_tarski(C_13),C_13) ),
    inference(resolution,[status(thm)],[c_30,c_108])).

tff(c_5055,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5031,c_127])).

tff(c_5113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_5055])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:53:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.86/2.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.19/2.23  
% 6.19/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.19/2.23  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_1 > #skF_4
% 6.19/2.23  
% 6.19/2.23  %Foreground sorts:
% 6.19/2.23  
% 6.19/2.23  
% 6.19/2.23  %Background operators:
% 6.19/2.23  
% 6.19/2.23  
% 6.19/2.23  %Foreground operators:
% 6.19/2.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.19/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.19/2.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.19/2.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.19/2.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.19/2.23  tff('#skF_7', type, '#skF_7': $i).
% 6.19/2.23  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.19/2.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.19/2.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.19/2.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.19/2.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.19/2.23  tff('#skF_5', type, '#skF_5': $i).
% 6.19/2.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.19/2.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.19/2.23  tff('#skF_6', type, '#skF_6': $i).
% 6.19/2.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.19/2.23  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.19/2.23  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.19/2.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.19/2.23  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.19/2.23  tff('#skF_8', type, '#skF_8': $i).
% 6.19/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.19/2.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.19/2.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.19/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.19/2.23  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.19/2.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 6.19/2.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.19/2.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.19/2.23  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.19/2.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.19/2.23  
% 6.19/2.25  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.19/2.25  tff(f_136, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 6.19/2.25  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.19/2.25  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.19/2.25  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.19/2.25  tff(f_125, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.19/2.25  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 6.19/2.25  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 6.19/2.25  tff(f_68, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.19/2.25  tff(f_74, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 6.19/2.25  tff(f_58, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 6.19/2.25  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 6.19/2.25  tff(f_49, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 6.19/2.25  tff(f_93, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.19/2.25  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.19/2.25  tff(c_84, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.19/2.25  tff(c_88, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.19/2.25  tff(c_281, plain, (![C_112, B_113, A_114]: (v5_relat_1(C_112, B_113) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_114, B_113))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.19/2.25  tff(c_290, plain, (v5_relat_1('#skF_8', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_88, c_281])).
% 6.19/2.25  tff(c_86, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.19/2.25  tff(c_216, plain, (![C_91, A_92, B_93]: (v1_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.19/2.25  tff(c_225, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_88, c_216])).
% 6.19/2.25  tff(c_92, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.19/2.25  tff(c_90, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.19/2.25  tff(c_868, plain, (![A_2130, B_2131, C_2132]: (k1_relset_1(A_2130, B_2131, C_2132)=k1_relat_1(C_2132) | ~m1_subset_1(C_2132, k1_zfmisc_1(k2_zfmisc_1(A_2130, B_2131))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.19/2.25  tff(c_879, plain, (k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_88, c_868])).
% 6.19/2.25  tff(c_1986, plain, (![B_4454, A_4455, C_4456]: (k1_xboole_0=B_4454 | k1_relset_1(A_4455, B_4454, C_4456)=A_4455 | ~v1_funct_2(C_4456, A_4455, B_4454) | ~m1_subset_1(C_4456, k1_zfmisc_1(k2_zfmisc_1(A_4455, B_4454))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.19/2.25  tff(c_1995, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_88, c_1986])).
% 6.19/2.25  tff(c_1999, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_879, c_1995])).
% 6.19/2.25  tff(c_2000, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_1999])).
% 6.19/2.25  tff(c_58, plain, (![B_29, A_28]: (r1_tarski(k2_relat_1(B_29), A_28) | ~v5_relat_1(B_29, A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.19/2.25  tff(c_1560, plain, (![B_3921, A_3922]: (r2_hidden(k1_funct_1(B_3921, A_3922), k2_relat_1(B_3921)) | ~r2_hidden(A_3922, k1_relat_1(B_3921)) | ~v1_funct_1(B_3921) | ~v1_relat_1(B_3921))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.19/2.25  tff(c_52, plain, (![A_23, B_24]: (m1_subset_1(A_23, k1_zfmisc_1(B_24)) | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.19/2.25  tff(c_327, plain, (![A_121, C_122, B_123]: (m1_subset_1(A_121, C_122) | ~m1_subset_1(B_123, k1_zfmisc_1(C_122)) | ~r2_hidden(A_121, B_123))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.19/2.25  tff(c_332, plain, (![A_121, B_24, A_23]: (m1_subset_1(A_121, B_24) | ~r2_hidden(A_121, A_23) | ~r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_52, c_327])).
% 6.19/2.25  tff(c_4857, plain, (![B_7712, A_7713, B_7714]: (m1_subset_1(k1_funct_1(B_7712, A_7713), B_7714) | ~r1_tarski(k2_relat_1(B_7712), B_7714) | ~r2_hidden(A_7713, k1_relat_1(B_7712)) | ~v1_funct_1(B_7712) | ~v1_relat_1(B_7712))), inference(resolution, [status(thm)], [c_1560, c_332])).
% 6.19/2.25  tff(c_4862, plain, (![B_7747, A_7748, A_7749]: (m1_subset_1(k1_funct_1(B_7747, A_7748), A_7749) | ~r2_hidden(A_7748, k1_relat_1(B_7747)) | ~v1_funct_1(B_7747) | ~v5_relat_1(B_7747, A_7749) | ~v1_relat_1(B_7747))), inference(resolution, [status(thm)], [c_58, c_4857])).
% 6.19/2.25  tff(c_4876, plain, (![A_7748, A_7749]: (m1_subset_1(k1_funct_1('#skF_8', A_7748), A_7749) | ~r2_hidden(A_7748, '#skF_5') | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', A_7749) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2000, c_4862])).
% 6.19/2.25  tff(c_4892, plain, (![A_7782, A_7783]: (m1_subset_1(k1_funct_1('#skF_8', A_7782), A_7783) | ~r2_hidden(A_7782, '#skF_5') | ~v5_relat_1('#skF_8', A_7783))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_92, c_4876])).
% 6.19/2.25  tff(c_46, plain, (![A_20]: (~v1_xboole_0(k1_tarski(A_20)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.19/2.25  tff(c_203, plain, (![A_87, B_88]: (r2_hidden(A_87, B_88) | v1_xboole_0(B_88) | ~m1_subset_1(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.19/2.25  tff(c_28, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.19/2.25  tff(c_207, plain, (![A_9, A_87]: (A_9=A_87 | v1_xboole_0(k1_tarski(A_9)) | ~m1_subset_1(A_87, k1_tarski(A_9)))), inference(resolution, [status(thm)], [c_203, c_28])).
% 6.19/2.25  tff(c_213, plain, (![A_9, A_87]: (A_9=A_87 | ~m1_subset_1(A_87, k1_tarski(A_9)))), inference(negUnitSimplification, [status(thm)], [c_46, c_207])).
% 6.19/2.25  tff(c_4985, plain, (![A_7848, A_7849]: (k1_funct_1('#skF_8', A_7848)=A_7849 | ~r2_hidden(A_7848, '#skF_5') | ~v5_relat_1('#skF_8', k1_tarski(A_7849)))), inference(resolution, [status(thm)], [c_4892, c_213])).
% 6.19/2.25  tff(c_5019, plain, (![A_7882]: (k1_funct_1('#skF_8', '#skF_7')=A_7882 | ~v5_relat_1('#skF_8', k1_tarski(A_7882)))), inference(resolution, [status(thm)], [c_86, c_4985])).
% 6.19/2.25  tff(c_5026, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_290, c_5019])).
% 6.19/2.25  tff(c_5030, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_5026])).
% 6.19/2.25  tff(c_5031, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1999])).
% 6.19/2.25  tff(c_30, plain, (![C_13]: (r2_hidden(C_13, k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.19/2.25  tff(c_108, plain, (![B_59, A_60]: (~r1_tarski(B_59, A_60) | ~r2_hidden(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.19/2.25  tff(c_127, plain, (![C_13]: (~r1_tarski(k1_tarski(C_13), C_13))), inference(resolution, [status(thm)], [c_30, c_108])).
% 6.19/2.25  tff(c_5055, plain, (~r1_tarski(k1_xboole_0, '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5031, c_127])).
% 6.19/2.25  tff(c_5113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_5055])).
% 6.19/2.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.19/2.25  
% 6.19/2.25  Inference rules
% 6.19/2.25  ----------------------
% 6.19/2.25  #Ref     : 0
% 6.19/2.25  #Sup     : 707
% 6.19/2.25  #Fact    : 2
% 6.19/2.25  #Define  : 0
% 6.19/2.25  #Split   : 18
% 6.19/2.25  #Chain   : 0
% 6.19/2.25  #Close   : 0
% 6.19/2.25  
% 6.19/2.25  Ordering : KBO
% 6.19/2.25  
% 6.19/2.25  Simplification rules
% 6.19/2.25  ----------------------
% 6.19/2.25  #Subsume      : 109
% 6.19/2.25  #Demod        : 161
% 6.19/2.25  #Tautology    : 188
% 6.19/2.25  #SimpNegUnit  : 7
% 6.19/2.25  #BackRed      : 8
% 6.19/2.25  
% 6.19/2.25  #Partial instantiations: 4427
% 6.19/2.25  #Strategies tried      : 1
% 6.19/2.25  
% 6.19/2.25  Timing (in seconds)
% 6.19/2.25  ----------------------
% 6.19/2.25  Preprocessing        : 0.36
% 6.19/2.25  Parsing              : 0.18
% 6.19/2.25  CNF conversion       : 0.03
% 6.19/2.25  Main loop            : 1.08
% 6.19/2.25  Inferencing          : 0.45
% 6.19/2.25  Reduction            : 0.29
% 6.19/2.25  Demodulation         : 0.20
% 6.19/2.25  BG Simplification    : 0.04
% 6.19/2.25  Subsumption          : 0.21
% 6.19/2.25  Abstraction          : 0.05
% 6.19/2.25  MUC search           : 0.00
% 6.19/2.25  Cooper               : 0.00
% 6.19/2.25  Total                : 1.47
% 6.19/2.25  Index Insertion      : 0.00
% 6.19/2.25  Index Deletion       : 0.00
% 6.19/2.25  Index Matching       : 0.00
% 6.19/2.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
