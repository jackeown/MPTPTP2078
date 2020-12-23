%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:11 EST 2020

% Result     : Theorem 8.36s
% Output     : CNFRefutation 8.56s
% Verified   : 
% Statistics : Number of formulae       :  218 (1947 expanded)
%              Number of leaves         :   37 ( 644 expanded)
%              Depth                    :   14
%              Number of atoms          :  385 (5777 expanded)
%              Number of equality atoms :  111 (1880 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_130,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(k2_relset_1(A,B,D),C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_110,axiom,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_32,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_11031,plain,(
    ! [B_870,A_871] :
      ( v1_relat_1(B_870)
      | ~ m1_subset_1(B_870,k1_zfmisc_1(A_871))
      | ~ v1_relat_1(A_871) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_11037,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_11031])).

tff(c_11044,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_11037])).

tff(c_11085,plain,(
    ! [C_876,A_877,B_878] :
      ( v4_relat_1(C_876,A_877)
      | ~ m1_subset_1(C_876,k1_zfmisc_1(k2_zfmisc_1(A_877,B_878))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_11104,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_11085])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_11314,plain,(
    ! [A_916,B_917,C_918] :
      ( k2_relset_1(A_916,B_917,C_918) = k2_relat_1(C_918)
      | ~ m1_subset_1(C_918,k1_zfmisc_1(k2_zfmisc_1(A_916,B_917))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_11333,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_11314])).

tff(c_60,plain,(
    r1_tarski(k2_relset_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_11336,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11333,c_60])).

tff(c_11510,plain,(
    ! [C_947,A_948,B_949] :
      ( m1_subset_1(C_947,k1_zfmisc_1(k2_zfmisc_1(A_948,B_949)))
      | ~ r1_tarski(k2_relat_1(C_947),B_949)
      | ~ r1_tarski(k1_relat_1(C_947),A_948)
      | ~ v1_relat_1(C_947) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_58,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_6304,plain,(
    ! [A_552,B_553,C_554] :
      ( k1_relset_1(A_552,B_553,C_554) = k1_relat_1(C_554)
      | ~ m1_subset_1(C_554,k1_zfmisc_1(k2_zfmisc_1(A_552,B_553))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6323,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_6304])).

tff(c_8664,plain,(
    ! [B_734,A_735,C_736] :
      ( k1_xboole_0 = B_734
      | k1_relset_1(A_735,B_734,C_736) = A_735
      | ~ v1_funct_2(C_736,A_735,B_734)
      | ~ m1_subset_1(C_736,k1_zfmisc_1(k2_zfmisc_1(A_735,B_734))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_8677,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_8664])).

tff(c_8689,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6323,c_8677])).

tff(c_8690,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_8689])).

tff(c_148,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_154,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_148])).

tff(c_161,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_154])).

tff(c_3109,plain,(
    ! [A_330,B_331,C_332] :
      ( k1_relset_1(A_330,B_331,C_332) = k1_relat_1(C_332)
      | ~ m1_subset_1(C_332,k1_zfmisc_1(k2_zfmisc_1(A_330,B_331))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3128,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_3109])).

tff(c_3317,plain,(
    ! [B_358,A_359,C_360] :
      ( k1_xboole_0 = B_358
      | k1_relset_1(A_359,B_358,C_360) = A_359
      | ~ v1_funct_2(C_360,A_359,B_358)
      | ~ m1_subset_1(C_360,k1_zfmisc_1(k2_zfmisc_1(A_359,B_358))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_3330,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_3317])).

tff(c_3342,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3128,c_3330])).

tff(c_3343,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3342])).

tff(c_3039,plain,(
    ! [A_321,B_322,C_323] :
      ( k2_relset_1(A_321,B_322,C_323) = k2_relat_1(C_323)
      | ~ m1_subset_1(C_323,k1_zfmisc_1(k2_zfmisc_1(A_321,B_322))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3058,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_3039])).

tff(c_3062,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3058,c_60])).

tff(c_3152,plain,(
    ! [C_337,A_338,B_339] :
      ( m1_subset_1(C_337,k1_zfmisc_1(k2_zfmisc_1(A_338,B_339)))
      | ~ r1_tarski(k2_relat_1(C_337),B_339)
      | ~ r1_tarski(k1_relat_1(C_337),A_338)
      | ~ v1_relat_1(C_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4653,plain,(
    ! [C_453,A_454,B_455] :
      ( r1_tarski(C_453,k2_zfmisc_1(A_454,B_455))
      | ~ r1_tarski(k2_relat_1(C_453),B_455)
      | ~ r1_tarski(k1_relat_1(C_453),A_454)
      | ~ v1_relat_1(C_453) ) ),
    inference(resolution,[status(thm)],[c_3152,c_20])).

tff(c_4655,plain,(
    ! [A_454] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_454,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_454)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3062,c_4653])).

tff(c_4663,plain,(
    ! [A_456] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_456,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_456) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_3343,c_4655])).

tff(c_22,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3127,plain,(
    ! [A_330,B_331,A_8] :
      ( k1_relset_1(A_330,B_331,A_8) = k1_relat_1(A_8)
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_330,B_331)) ) ),
    inference(resolution,[status(thm)],[c_22,c_3109])).

tff(c_4666,plain,(
    ! [A_456] :
      ( k1_relset_1(A_456,'#skF_3','#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',A_456) ) ),
    inference(resolution,[status(thm)],[c_4663,c_3127])).

tff(c_4696,plain,(
    ! [A_457] :
      ( k1_relset_1(A_457,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_457) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3343,c_4666])).

tff(c_4701,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_4696])).

tff(c_4661,plain,(
    ! [A_454] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_454,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_454) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_3343,c_4655])).

tff(c_3471,plain,(
    ! [B_371,C_372,A_373] :
      ( k1_xboole_0 = B_371
      | v1_funct_2(C_372,A_373,B_371)
      | k1_relset_1(A_373,B_371,C_372) != A_373
      | ~ m1_subset_1(C_372,k1_zfmisc_1(k2_zfmisc_1(A_373,B_371))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_5889,plain,(
    ! [B_504,A_505,A_506] :
      ( k1_xboole_0 = B_504
      | v1_funct_2(A_505,A_506,B_504)
      | k1_relset_1(A_506,B_504,A_505) != A_506
      | ~ r1_tarski(A_505,k2_zfmisc_1(A_506,B_504)) ) ),
    inference(resolution,[status(thm)],[c_22,c_3471])).

tff(c_5918,plain,(
    ! [A_454] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2('#skF_4',A_454,'#skF_3')
      | k1_relset_1(A_454,'#skF_3','#skF_4') != A_454
      | ~ r1_tarski('#skF_1',A_454) ) ),
    inference(resolution,[status(thm)],[c_4661,c_5889])).

tff(c_5952,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5918])).

tff(c_6073,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5952,c_8])).

tff(c_2726,plain,(
    ! [B_270,A_271] :
      ( B_270 = A_271
      | ~ r1_tarski(B_270,A_271)
      | ~ r1_tarski(A_271,B_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2736,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_60,c_2726])).

tff(c_2875,plain,(
    ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2736])).

tff(c_3060,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3058,c_2875])).

tff(c_6083,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6073,c_3060])).

tff(c_6086,plain,(
    ! [A_513] :
      ( v1_funct_2('#skF_4',A_513,'#skF_3')
      | k1_relset_1(A_513,'#skF_3','#skF_4') != A_513
      | ~ r1_tarski('#skF_1',A_513) ) ),
    inference(splitRight,[status(thm)],[c_5918])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_56,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_68,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_56])).

tff(c_147,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_6092,plain,
    ( k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_6086,c_147])).

tff(c_6097,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4701,c_6092])).

tff(c_6098,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2736])).

tff(c_6193,plain,(
    ! [A_533,B_534,C_535] :
      ( k2_relset_1(A_533,B_534,C_535) = k2_relat_1(C_535)
      | ~ m1_subset_1(C_535,k1_zfmisc_1(k2_zfmisc_1(A_533,B_534))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6203,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_6193])).

tff(c_6213,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6098,c_6203])).

tff(c_8482,plain,(
    ! [C_715,A_716,B_717] :
      ( m1_subset_1(C_715,k1_zfmisc_1(k2_zfmisc_1(A_716,B_717)))
      | ~ r1_tarski(k2_relat_1(C_715),B_717)
      | ~ r1_tarski(k1_relat_1(C_715),A_716)
      | ~ v1_relat_1(C_715) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_9563,plain,(
    ! [C_804,A_805,B_806] :
      ( r1_tarski(C_804,k2_zfmisc_1(A_805,B_806))
      | ~ r1_tarski(k2_relat_1(C_804),B_806)
      | ~ r1_tarski(k1_relat_1(C_804),A_805)
      | ~ v1_relat_1(C_804) ) ),
    inference(resolution,[status(thm)],[c_8482,c_20])).

tff(c_9565,plain,(
    ! [A_805,B_806] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_805,B_806))
      | ~ r1_tarski('#skF_3',B_806)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_805)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6213,c_9563])).

tff(c_9572,plain,(
    ! [A_807,B_808] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_807,B_808))
      | ~ r1_tarski('#skF_3',B_808)
      | ~ r1_tarski('#skF_1',A_807) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_8690,c_9565])).

tff(c_6322,plain,(
    ! [A_552,B_553,A_8] :
      ( k1_relset_1(A_552,B_553,A_8) = k1_relat_1(A_8)
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_552,B_553)) ) ),
    inference(resolution,[status(thm)],[c_22,c_6304])).

tff(c_9578,plain,(
    ! [A_807,B_808] :
      ( k1_relset_1(A_807,B_808,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_3',B_808)
      | ~ r1_tarski('#skF_1',A_807) ) ),
    inference(resolution,[status(thm)],[c_9572,c_6322])).

tff(c_9634,plain,(
    ! [A_814,B_815] :
      ( k1_relset_1(A_814,B_815,'#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_3',B_815)
      | ~ r1_tarski('#skF_1',A_814) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8690,c_9578])).

tff(c_9639,plain,(
    ! [A_816] :
      ( k1_relset_1(A_816,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_816) ) ),
    inference(resolution,[status(thm)],[c_6,c_9634])).

tff(c_9644,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_9639])).

tff(c_9722,plain,(
    ! [C_822,A_823] :
      ( r1_tarski(C_822,k2_zfmisc_1(A_823,k2_relat_1(C_822)))
      | ~ r1_tarski(k1_relat_1(C_822),A_823)
      | ~ v1_relat_1(C_822) ) ),
    inference(resolution,[status(thm)],[c_6,c_9563])).

tff(c_9769,plain,(
    ! [A_823] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_823,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_823)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6213,c_9722])).

tff(c_9800,plain,(
    ! [A_824] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_824,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_824) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_8690,c_9769])).

tff(c_8575,plain,(
    ! [B_724,C_725,A_726] :
      ( k1_xboole_0 = B_724
      | v1_funct_2(C_725,A_726,B_724)
      | k1_relset_1(A_726,B_724,C_725) != A_726
      | ~ m1_subset_1(C_725,k1_zfmisc_1(k2_zfmisc_1(A_726,B_724))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_8597,plain,(
    ! [B_724,A_8,A_726] :
      ( k1_xboole_0 = B_724
      | v1_funct_2(A_8,A_726,B_724)
      | k1_relset_1(A_726,B_724,A_8) != A_726
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_726,B_724)) ) ),
    inference(resolution,[status(thm)],[c_22,c_8575])).

tff(c_9825,plain,(
    ! [A_824] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2('#skF_4',A_824,'#skF_3')
      | k1_relset_1(A_824,'#skF_3','#skF_4') != A_824
      | ~ r1_tarski('#skF_1',A_824) ) ),
    inference(resolution,[status(thm)],[c_9800,c_8597])).

tff(c_10005,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_9825])).

tff(c_14,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_9140,plain,(
    ! [C_779,A_780] :
      ( m1_subset_1(C_779,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_779),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_779),A_780)
      | ~ v1_relat_1(C_779) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_8482])).

tff(c_9142,plain,(
    ! [A_780] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_780)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6213,c_9140])).

tff(c_9144,plain,(
    ! [A_780] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',k1_xboole_0)
      | ~ r1_tarski('#skF_1',A_780) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_8690,c_9142])).

tff(c_9145,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_9144])).

tff(c_10025,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10005,c_9145])).

tff(c_10077,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10025])).

tff(c_10080,plain,(
    ! [A_835] :
      ( v1_funct_2('#skF_4',A_835,'#skF_3')
      | k1_relset_1(A_835,'#skF_3','#skF_4') != A_835
      | ~ r1_tarski('#skF_1',A_835) ) ),
    inference(splitRight,[status(thm)],[c_9825])).

tff(c_10086,plain,
    ( k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_10080,c_147])).

tff(c_10091,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9644,c_10086])).

tff(c_10093,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_9144])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10106,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_10093,c_2])).

tff(c_10122,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10106])).

tff(c_2749,plain,(
    ! [C_275,A_276,B_277] :
      ( v4_relat_1(C_275,A_276)
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(A_276,B_277))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2771,plain,(
    ! [C_279,A_280] :
      ( v4_relat_1(C_279,A_280)
      | ~ m1_subset_1(C_279,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2749])).

tff(c_2778,plain,(
    ! [A_8,A_280] :
      ( v4_relat_1(A_8,A_280)
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_2771])).

tff(c_8703,plain,(
    ! [A_16] :
      ( r1_tarski('#skF_1',A_16)
      | ~ v4_relat_1('#skF_4',A_16)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8690,c_30])).

tff(c_8725,plain,(
    ! [A_737] :
      ( r1_tarski('#skF_1',A_737)
      | ~ v4_relat_1('#skF_4',A_737) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_8703])).

tff(c_8737,plain,(
    ! [A_280] :
      ( r1_tarski('#skF_1',A_280)
      | ~ r1_tarski('#skF_4',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2778,c_8725])).

tff(c_8760,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_8737])).

tff(c_10138,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10122,c_8760])).

tff(c_10470,plain,(
    ! [A_852] : k2_zfmisc_1(A_852,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10122,c_10122,c_14])).

tff(c_10176,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10122,c_8])).

tff(c_10280,plain,(
    ! [C_842,A_843,B_844] :
      ( r1_tarski(C_842,k2_zfmisc_1(A_843,B_844))
      | ~ r1_tarski(k2_relat_1(C_842),B_844)
      | ~ r1_tarski(k1_relat_1(C_842),A_843)
      | ~ v1_relat_1(C_842) ) ),
    inference(resolution,[status(thm)],[c_8482,c_20])).

tff(c_10282,plain,(
    ! [A_843,B_844] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_843,B_844))
      | ~ r1_tarski('#skF_3',B_844)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_843)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6213,c_10280])).

tff(c_10287,plain,(
    ! [A_843,B_844] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_843,B_844))
      | ~ r1_tarski('#skF_1',A_843) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_8690,c_10176,c_10282])).

tff(c_10481,plain,(
    ! [A_852] :
      ( r1_tarski('#skF_4','#skF_3')
      | ~ r1_tarski('#skF_1',A_852) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10470,c_10287])).

tff(c_10574,plain,(
    ! [A_854] : ~ r1_tarski('#skF_1',A_854) ),
    inference(negUnitSimplification,[status(thm)],[c_10138,c_10481])).

tff(c_10579,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_10574])).

tff(c_10580,plain,(
    ! [A_280] : r1_tarski('#skF_1',A_280) ),
    inference(splitRight,[status(thm)],[c_8737])).

tff(c_10585,plain,(
    ! [A_855] : r1_tarski('#skF_1',A_855) ),
    inference(splitRight,[status(thm)],[c_8737])).

tff(c_10,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10641,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10585,c_10])).

tff(c_10581,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_8737])).

tff(c_10691,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10641,c_10581])).

tff(c_10693,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_10691,c_2])).

tff(c_10699,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10580,c_10693])).

tff(c_80,plain,(
    ! [A_40] : k2_zfmisc_1(A_40,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_84,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_32])).

tff(c_18,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2769,plain,(
    ! [A_276] : v4_relat_1(k1_xboole_0,A_276) ),
    inference(resolution,[status(thm)],[c_18,c_2749])).

tff(c_2805,plain,(
    ! [B_286,A_287] :
      ( r1_tarski(k1_relat_1(B_286),A_287)
      | ~ v4_relat_1(B_286,A_287)
      | ~ v1_relat_1(B_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2836,plain,(
    ! [B_290] :
      ( k1_relat_1(B_290) = k1_xboole_0
      | ~ v4_relat_1(B_290,k1_xboole_0)
      | ~ v1_relat_1(B_290) ) ),
    inference(resolution,[status(thm)],[c_2805,c_10])).

tff(c_2848,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2769,c_2836])).

tff(c_2855,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2848])).

tff(c_6321,plain,(
    ! [A_552,B_553] : k1_relset_1(A_552,B_553,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_6304])).

tff(c_6325,plain,(
    ! [A_552,B_553] : k1_relset_1(A_552,B_553,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2855,c_6321])).

tff(c_16,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_48,plain,(
    ! [C_34,B_33] :
      ( v1_funct_2(C_34,k1_xboole_0,B_33)
      | k1_relset_1(k1_xboole_0,B_33,C_34) != k1_xboole_0
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_8458,plain,(
    ! [C_712,B_713] :
      ( v1_funct_2(C_712,k1_xboole_0,B_713)
      | k1_relset_1(k1_xboole_0,B_713,C_712) != k1_xboole_0
      | ~ m1_subset_1(C_712,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_48])).

tff(c_8464,plain,(
    ! [B_713] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_713)
      | k1_relset_1(k1_xboole_0,B_713,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_8458])).

tff(c_8468,plain,(
    ! [B_713] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_713) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6325,c_8464])).

tff(c_10646,plain,(
    ! [B_713] : v1_funct_2('#skF_1','#skF_1',B_713) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10641,c_10641,c_8468])).

tff(c_10957,plain,(
    ! [B_713] : v1_funct_2('#skF_4','#skF_4',B_713) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10699,c_10699,c_10646])).

tff(c_10715,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10699,c_147])).

tff(c_11024,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10957,c_10715])).

tff(c_11025,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_11530,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_11510,c_11025])).

tff(c_11550,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11044,c_11336,c_11530])).

tff(c_11554,plain,
    ( ~ v4_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_11550])).

tff(c_11558,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11044,c_11104,c_11554])).

tff(c_11559,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_11561,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11559,c_8])).

tff(c_11573,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11559,c_11559,c_16])).

tff(c_11560,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_11566,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11559,c_11560])).

tff(c_11619,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11573,c_11566,c_62])).

tff(c_11623,plain,(
    ! [A_958,B_959] :
      ( r1_tarski(A_958,B_959)
      | ~ m1_subset_1(A_958,k1_zfmisc_1(B_959)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_11634,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_11619,c_11623])).

tff(c_11651,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_11634,c_2])).

tff(c_11657,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11561,c_11651])).

tff(c_11583,plain,(
    ! [A_7] : m1_subset_1('#skF_1',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11559,c_18])).

tff(c_11665,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11657,c_11583])).

tff(c_11667,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_4',B_6) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11657,c_11657,c_11573])).

tff(c_11812,plain,(
    ! [C_982,A_983,B_984] :
      ( v4_relat_1(C_982,A_983)
      | ~ m1_subset_1(C_982,k1_zfmisc_1(k2_zfmisc_1(A_983,B_984))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_11854,plain,(
    ! [A_992,A_993,B_994] :
      ( v4_relat_1(A_992,A_993)
      | ~ r1_tarski(A_992,k2_zfmisc_1(A_993,B_994)) ) ),
    inference(resolution,[status(thm)],[c_22,c_11812])).

tff(c_11871,plain,(
    ! [A_993,B_994] : v4_relat_1(k2_zfmisc_1(A_993,B_994),A_993) ),
    inference(resolution,[status(thm)],[c_6,c_11854])).

tff(c_11881,plain,(
    ! [B_997,A_998] :
      ( r1_tarski(k1_relat_1(B_997),A_998)
      | ~ v4_relat_1(B_997,A_998)
      | ~ v1_relat_1(B_997) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_11605,plain,(
    ! [A_4] :
      ( A_4 = '#skF_1'
      | ~ r1_tarski(A_4,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11559,c_11559,c_10])).

tff(c_11662,plain,(
    ! [A_4] :
      ( A_4 = '#skF_4'
      | ~ r1_tarski(A_4,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11657,c_11657,c_11605])).

tff(c_11931,plain,(
    ! [B_1004] :
      ( k1_relat_1(B_1004) = '#skF_4'
      | ~ v4_relat_1(B_1004,'#skF_4')
      | ~ v1_relat_1(B_1004) ) ),
    inference(resolution,[status(thm)],[c_11881,c_11662])).

tff(c_11935,plain,(
    ! [B_994] :
      ( k1_relat_1(k2_zfmisc_1('#skF_4',B_994)) = '#skF_4'
      | ~ v1_relat_1(k2_zfmisc_1('#skF_4',B_994)) ) ),
    inference(resolution,[status(thm)],[c_11871,c_11931])).

tff(c_11946,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_11667,c_11935])).

tff(c_12042,plain,(
    ! [A_1021,B_1022,C_1023] :
      ( k1_relset_1(A_1021,B_1022,C_1023) = k1_relat_1(C_1023)
      | ~ m1_subset_1(C_1023,k1_zfmisc_1(k2_zfmisc_1(A_1021,B_1022))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_12049,plain,(
    ! [A_1021,B_1022] : k1_relset_1(A_1021,B_1022,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_11665,c_12042])).

tff(c_12058,plain,(
    ! [A_1021,B_1022] : k1_relset_1(A_1021,B_1022,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11946,c_12049])).

tff(c_11671,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11657,c_11559])).

tff(c_72,plain,(
    ! [C_34,B_33] :
      ( v1_funct_2(C_34,k1_xboole_0,B_33)
      | k1_relset_1(k1_xboole_0,B_33,C_34) != k1_xboole_0
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_48])).

tff(c_12377,plain,(
    ! [C_1068,B_1069] :
      ( v1_funct_2(C_1068,'#skF_4',B_1069)
      | k1_relset_1('#skF_4',B_1069,C_1068) != '#skF_4'
      | ~ m1_subset_1(C_1068,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11671,c_11671,c_11671,c_11671,c_72])).

tff(c_12380,plain,(
    ! [B_1069] :
      ( v1_funct_2('#skF_4','#skF_4',B_1069)
      | k1_relset_1('#skF_4',B_1069,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_11665,c_12377])).

tff(c_12386,plain,(
    ! [B_1069] : v1_funct_2('#skF_4','#skF_4',B_1069) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12058,c_12380])).

tff(c_11678,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11657,c_11657,c_68])).

tff(c_11679,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_11678])).

tff(c_12391,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12386,c_11679])).

tff(c_12392,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_11678])).

tff(c_12479,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11665,c_11667,c_12392])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n005.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 17:24:32 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.36/2.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.36/2.90  
% 8.36/2.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.36/2.91  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.36/2.91  
% 8.36/2.91  %Foreground sorts:
% 8.36/2.91  
% 8.36/2.91  
% 8.36/2.91  %Background operators:
% 8.36/2.91  
% 8.36/2.91  
% 8.36/2.91  %Foreground operators:
% 8.36/2.91  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.36/2.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.36/2.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.36/2.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.36/2.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.36/2.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.36/2.91  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.36/2.91  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.36/2.91  tff('#skF_2', type, '#skF_2': $i).
% 8.36/2.91  tff('#skF_3', type, '#skF_3': $i).
% 8.36/2.91  tff('#skF_1', type, '#skF_1': $i).
% 8.36/2.91  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.36/2.91  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.36/2.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.36/2.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.36/2.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.36/2.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.36/2.91  tff('#skF_4', type, '#skF_4': $i).
% 8.36/2.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.36/2.91  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.36/2.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.36/2.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.36/2.91  
% 8.56/2.94  tff(f_70, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.56/2.94  tff(f_130, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 8.56/2.94  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.56/2.94  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.56/2.94  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 8.56/2.94  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.56/2.94  tff(f_92, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 8.56/2.94  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.56/2.94  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.56/2.94  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.56/2.94  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 8.56/2.94  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.56/2.94  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.56/2.94  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 8.56/2.94  tff(f_45, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 8.56/2.94  tff(c_32, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.56/2.94  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.56/2.94  tff(c_11031, plain, (![B_870, A_871]: (v1_relat_1(B_870) | ~m1_subset_1(B_870, k1_zfmisc_1(A_871)) | ~v1_relat_1(A_871))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.56/2.94  tff(c_11037, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_11031])).
% 8.56/2.94  tff(c_11044, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_11037])).
% 8.56/2.94  tff(c_11085, plain, (![C_876, A_877, B_878]: (v4_relat_1(C_876, A_877) | ~m1_subset_1(C_876, k1_zfmisc_1(k2_zfmisc_1(A_877, B_878))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.56/2.94  tff(c_11104, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_11085])).
% 8.56/2.94  tff(c_30, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(B_17), A_16) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.56/2.94  tff(c_11314, plain, (![A_916, B_917, C_918]: (k2_relset_1(A_916, B_917, C_918)=k2_relat_1(C_918) | ~m1_subset_1(C_918, k1_zfmisc_1(k2_zfmisc_1(A_916, B_917))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.56/2.94  tff(c_11333, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_11314])).
% 8.56/2.94  tff(c_60, plain, (r1_tarski(k2_relset_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.56/2.94  tff(c_11336, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11333, c_60])).
% 8.56/2.94  tff(c_11510, plain, (![C_947, A_948, B_949]: (m1_subset_1(C_947, k1_zfmisc_1(k2_zfmisc_1(A_948, B_949))) | ~r1_tarski(k2_relat_1(C_947), B_949) | ~r1_tarski(k1_relat_1(C_947), A_948) | ~v1_relat_1(C_947))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.56/2.94  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.56/2.94  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.56/2.94  tff(c_58, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.56/2.94  tff(c_78, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_58])).
% 8.56/2.94  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.56/2.94  tff(c_6304, plain, (![A_552, B_553, C_554]: (k1_relset_1(A_552, B_553, C_554)=k1_relat_1(C_554) | ~m1_subset_1(C_554, k1_zfmisc_1(k2_zfmisc_1(A_552, B_553))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.56/2.94  tff(c_6323, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_6304])).
% 8.56/2.94  tff(c_8664, plain, (![B_734, A_735, C_736]: (k1_xboole_0=B_734 | k1_relset_1(A_735, B_734, C_736)=A_735 | ~v1_funct_2(C_736, A_735, B_734) | ~m1_subset_1(C_736, k1_zfmisc_1(k2_zfmisc_1(A_735, B_734))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.56/2.94  tff(c_8677, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_8664])).
% 8.56/2.94  tff(c_8689, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_6323, c_8677])).
% 8.56/2.94  tff(c_8690, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_78, c_8689])).
% 8.56/2.94  tff(c_148, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.56/2.94  tff(c_154, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_148])).
% 8.56/2.94  tff(c_161, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_154])).
% 8.56/2.94  tff(c_3109, plain, (![A_330, B_331, C_332]: (k1_relset_1(A_330, B_331, C_332)=k1_relat_1(C_332) | ~m1_subset_1(C_332, k1_zfmisc_1(k2_zfmisc_1(A_330, B_331))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.56/2.94  tff(c_3128, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_3109])).
% 8.56/2.94  tff(c_3317, plain, (![B_358, A_359, C_360]: (k1_xboole_0=B_358 | k1_relset_1(A_359, B_358, C_360)=A_359 | ~v1_funct_2(C_360, A_359, B_358) | ~m1_subset_1(C_360, k1_zfmisc_1(k2_zfmisc_1(A_359, B_358))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.56/2.94  tff(c_3330, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_3317])).
% 8.56/2.94  tff(c_3342, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3128, c_3330])).
% 8.56/2.94  tff(c_3343, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_78, c_3342])).
% 8.56/2.94  tff(c_3039, plain, (![A_321, B_322, C_323]: (k2_relset_1(A_321, B_322, C_323)=k2_relat_1(C_323) | ~m1_subset_1(C_323, k1_zfmisc_1(k2_zfmisc_1(A_321, B_322))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.56/2.94  tff(c_3058, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_3039])).
% 8.56/2.94  tff(c_3062, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3058, c_60])).
% 8.56/2.94  tff(c_3152, plain, (![C_337, A_338, B_339]: (m1_subset_1(C_337, k1_zfmisc_1(k2_zfmisc_1(A_338, B_339))) | ~r1_tarski(k2_relat_1(C_337), B_339) | ~r1_tarski(k1_relat_1(C_337), A_338) | ~v1_relat_1(C_337))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.56/2.94  tff(c_20, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.56/2.94  tff(c_4653, plain, (![C_453, A_454, B_455]: (r1_tarski(C_453, k2_zfmisc_1(A_454, B_455)) | ~r1_tarski(k2_relat_1(C_453), B_455) | ~r1_tarski(k1_relat_1(C_453), A_454) | ~v1_relat_1(C_453))), inference(resolution, [status(thm)], [c_3152, c_20])).
% 8.56/2.94  tff(c_4655, plain, (![A_454]: (r1_tarski('#skF_4', k2_zfmisc_1(A_454, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_454) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_3062, c_4653])).
% 8.56/2.94  tff(c_4663, plain, (![A_456]: (r1_tarski('#skF_4', k2_zfmisc_1(A_456, '#skF_3')) | ~r1_tarski('#skF_1', A_456))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_3343, c_4655])).
% 8.56/2.94  tff(c_22, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.56/2.94  tff(c_3127, plain, (![A_330, B_331, A_8]: (k1_relset_1(A_330, B_331, A_8)=k1_relat_1(A_8) | ~r1_tarski(A_8, k2_zfmisc_1(A_330, B_331)))), inference(resolution, [status(thm)], [c_22, c_3109])).
% 8.56/2.94  tff(c_4666, plain, (![A_456]: (k1_relset_1(A_456, '#skF_3', '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_1', A_456))), inference(resolution, [status(thm)], [c_4663, c_3127])).
% 8.56/2.94  tff(c_4696, plain, (![A_457]: (k1_relset_1(A_457, '#skF_3', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_457))), inference(demodulation, [status(thm), theory('equality')], [c_3343, c_4666])).
% 8.56/2.94  tff(c_4701, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_6, c_4696])).
% 8.56/2.94  tff(c_4661, plain, (![A_454]: (r1_tarski('#skF_4', k2_zfmisc_1(A_454, '#skF_3')) | ~r1_tarski('#skF_1', A_454))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_3343, c_4655])).
% 8.56/2.94  tff(c_3471, plain, (![B_371, C_372, A_373]: (k1_xboole_0=B_371 | v1_funct_2(C_372, A_373, B_371) | k1_relset_1(A_373, B_371, C_372)!=A_373 | ~m1_subset_1(C_372, k1_zfmisc_1(k2_zfmisc_1(A_373, B_371))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.56/2.94  tff(c_5889, plain, (![B_504, A_505, A_506]: (k1_xboole_0=B_504 | v1_funct_2(A_505, A_506, B_504) | k1_relset_1(A_506, B_504, A_505)!=A_506 | ~r1_tarski(A_505, k2_zfmisc_1(A_506, B_504)))), inference(resolution, [status(thm)], [c_22, c_3471])).
% 8.56/2.94  tff(c_5918, plain, (![A_454]: (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', A_454, '#skF_3') | k1_relset_1(A_454, '#skF_3', '#skF_4')!=A_454 | ~r1_tarski('#skF_1', A_454))), inference(resolution, [status(thm)], [c_4661, c_5889])).
% 8.56/2.94  tff(c_5952, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_5918])).
% 8.56/2.94  tff(c_6073, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_5952, c_8])).
% 8.56/2.94  tff(c_2726, plain, (![B_270, A_271]: (B_270=A_271 | ~r1_tarski(B_270, A_271) | ~r1_tarski(A_271, B_270))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.56/2.94  tff(c_2736, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_60, c_2726])).
% 8.56/2.94  tff(c_2875, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_2736])).
% 8.56/2.94  tff(c_3060, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3058, c_2875])).
% 8.56/2.94  tff(c_6083, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6073, c_3060])).
% 8.56/2.94  tff(c_6086, plain, (![A_513]: (v1_funct_2('#skF_4', A_513, '#skF_3') | k1_relset_1(A_513, '#skF_3', '#skF_4')!=A_513 | ~r1_tarski('#skF_1', A_513))), inference(splitRight, [status(thm)], [c_5918])).
% 8.56/2.94  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.56/2.94  tff(c_56, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.56/2.94  tff(c_68, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_56])).
% 8.56/2.94  tff(c_147, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_68])).
% 8.56/2.94  tff(c_6092, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_6086, c_147])).
% 8.56/2.94  tff(c_6097, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_4701, c_6092])).
% 8.56/2.94  tff(c_6098, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_2736])).
% 8.56/2.94  tff(c_6193, plain, (![A_533, B_534, C_535]: (k2_relset_1(A_533, B_534, C_535)=k2_relat_1(C_535) | ~m1_subset_1(C_535, k1_zfmisc_1(k2_zfmisc_1(A_533, B_534))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.56/2.94  tff(c_6203, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_6193])).
% 8.56/2.94  tff(c_6213, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6098, c_6203])).
% 8.56/2.94  tff(c_8482, plain, (![C_715, A_716, B_717]: (m1_subset_1(C_715, k1_zfmisc_1(k2_zfmisc_1(A_716, B_717))) | ~r1_tarski(k2_relat_1(C_715), B_717) | ~r1_tarski(k1_relat_1(C_715), A_716) | ~v1_relat_1(C_715))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.56/2.94  tff(c_9563, plain, (![C_804, A_805, B_806]: (r1_tarski(C_804, k2_zfmisc_1(A_805, B_806)) | ~r1_tarski(k2_relat_1(C_804), B_806) | ~r1_tarski(k1_relat_1(C_804), A_805) | ~v1_relat_1(C_804))), inference(resolution, [status(thm)], [c_8482, c_20])).
% 8.56/2.94  tff(c_9565, plain, (![A_805, B_806]: (r1_tarski('#skF_4', k2_zfmisc_1(A_805, B_806)) | ~r1_tarski('#skF_3', B_806) | ~r1_tarski(k1_relat_1('#skF_4'), A_805) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6213, c_9563])).
% 8.56/2.94  tff(c_9572, plain, (![A_807, B_808]: (r1_tarski('#skF_4', k2_zfmisc_1(A_807, B_808)) | ~r1_tarski('#skF_3', B_808) | ~r1_tarski('#skF_1', A_807))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_8690, c_9565])).
% 8.56/2.94  tff(c_6322, plain, (![A_552, B_553, A_8]: (k1_relset_1(A_552, B_553, A_8)=k1_relat_1(A_8) | ~r1_tarski(A_8, k2_zfmisc_1(A_552, B_553)))), inference(resolution, [status(thm)], [c_22, c_6304])).
% 8.56/2.94  tff(c_9578, plain, (![A_807, B_808]: (k1_relset_1(A_807, B_808, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_3', B_808) | ~r1_tarski('#skF_1', A_807))), inference(resolution, [status(thm)], [c_9572, c_6322])).
% 8.56/2.94  tff(c_9634, plain, (![A_814, B_815]: (k1_relset_1(A_814, B_815, '#skF_4')='#skF_1' | ~r1_tarski('#skF_3', B_815) | ~r1_tarski('#skF_1', A_814))), inference(demodulation, [status(thm), theory('equality')], [c_8690, c_9578])).
% 8.56/2.94  tff(c_9639, plain, (![A_816]: (k1_relset_1(A_816, '#skF_3', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_816))), inference(resolution, [status(thm)], [c_6, c_9634])).
% 8.56/2.94  tff(c_9644, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_6, c_9639])).
% 8.56/2.94  tff(c_9722, plain, (![C_822, A_823]: (r1_tarski(C_822, k2_zfmisc_1(A_823, k2_relat_1(C_822))) | ~r1_tarski(k1_relat_1(C_822), A_823) | ~v1_relat_1(C_822))), inference(resolution, [status(thm)], [c_6, c_9563])).
% 8.56/2.94  tff(c_9769, plain, (![A_823]: (r1_tarski('#skF_4', k2_zfmisc_1(A_823, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_823) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6213, c_9722])).
% 8.56/2.94  tff(c_9800, plain, (![A_824]: (r1_tarski('#skF_4', k2_zfmisc_1(A_824, '#skF_3')) | ~r1_tarski('#skF_1', A_824))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_8690, c_9769])).
% 8.56/2.94  tff(c_8575, plain, (![B_724, C_725, A_726]: (k1_xboole_0=B_724 | v1_funct_2(C_725, A_726, B_724) | k1_relset_1(A_726, B_724, C_725)!=A_726 | ~m1_subset_1(C_725, k1_zfmisc_1(k2_zfmisc_1(A_726, B_724))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.56/2.94  tff(c_8597, plain, (![B_724, A_8, A_726]: (k1_xboole_0=B_724 | v1_funct_2(A_8, A_726, B_724) | k1_relset_1(A_726, B_724, A_8)!=A_726 | ~r1_tarski(A_8, k2_zfmisc_1(A_726, B_724)))), inference(resolution, [status(thm)], [c_22, c_8575])).
% 8.56/2.94  tff(c_9825, plain, (![A_824]: (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', A_824, '#skF_3') | k1_relset_1(A_824, '#skF_3', '#skF_4')!=A_824 | ~r1_tarski('#skF_1', A_824))), inference(resolution, [status(thm)], [c_9800, c_8597])).
% 8.56/2.94  tff(c_10005, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_9825])).
% 8.56/2.94  tff(c_14, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.56/2.94  tff(c_9140, plain, (![C_779, A_780]: (m1_subset_1(C_779, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_779), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_779), A_780) | ~v1_relat_1(C_779))), inference(superposition, [status(thm), theory('equality')], [c_14, c_8482])).
% 8.56/2.94  tff(c_9142, plain, (![A_780]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_4'), A_780) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6213, c_9140])).
% 8.56/2.94  tff(c_9144, plain, (![A_780]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_1', A_780))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_8690, c_9142])).
% 8.56/2.94  tff(c_9145, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_9144])).
% 8.56/2.94  tff(c_10025, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10005, c_9145])).
% 8.56/2.94  tff(c_10077, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_10025])).
% 8.56/2.94  tff(c_10080, plain, (![A_835]: (v1_funct_2('#skF_4', A_835, '#skF_3') | k1_relset_1(A_835, '#skF_3', '#skF_4')!=A_835 | ~r1_tarski('#skF_1', A_835))), inference(splitRight, [status(thm)], [c_9825])).
% 8.56/2.94  tff(c_10086, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_10080, c_147])).
% 8.56/2.94  tff(c_10091, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_9644, c_10086])).
% 8.56/2.94  tff(c_10093, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_9144])).
% 8.56/2.94  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.56/2.94  tff(c_10106, plain, (k1_xboole_0='#skF_3' | ~r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_10093, c_2])).
% 8.56/2.94  tff(c_10122, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10106])).
% 8.56/2.94  tff(c_2749, plain, (![C_275, A_276, B_277]: (v4_relat_1(C_275, A_276) | ~m1_subset_1(C_275, k1_zfmisc_1(k2_zfmisc_1(A_276, B_277))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.56/2.94  tff(c_2771, plain, (![C_279, A_280]: (v4_relat_1(C_279, A_280) | ~m1_subset_1(C_279, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_2749])).
% 8.56/2.94  tff(c_2778, plain, (![A_8, A_280]: (v4_relat_1(A_8, A_280) | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_2771])).
% 8.56/2.94  tff(c_8703, plain, (![A_16]: (r1_tarski('#skF_1', A_16) | ~v4_relat_1('#skF_4', A_16) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8690, c_30])).
% 8.56/2.94  tff(c_8725, plain, (![A_737]: (r1_tarski('#skF_1', A_737) | ~v4_relat_1('#skF_4', A_737))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_8703])).
% 8.56/2.94  tff(c_8737, plain, (![A_280]: (r1_tarski('#skF_1', A_280) | ~r1_tarski('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_2778, c_8725])).
% 8.56/2.94  tff(c_8760, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_8737])).
% 8.56/2.94  tff(c_10138, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10122, c_8760])).
% 8.56/2.94  tff(c_10470, plain, (![A_852]: (k2_zfmisc_1(A_852, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10122, c_10122, c_14])).
% 8.56/2.94  tff(c_10176, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_10122, c_8])).
% 8.56/2.94  tff(c_10280, plain, (![C_842, A_843, B_844]: (r1_tarski(C_842, k2_zfmisc_1(A_843, B_844)) | ~r1_tarski(k2_relat_1(C_842), B_844) | ~r1_tarski(k1_relat_1(C_842), A_843) | ~v1_relat_1(C_842))), inference(resolution, [status(thm)], [c_8482, c_20])).
% 8.56/2.94  tff(c_10282, plain, (![A_843, B_844]: (r1_tarski('#skF_4', k2_zfmisc_1(A_843, B_844)) | ~r1_tarski('#skF_3', B_844) | ~r1_tarski(k1_relat_1('#skF_4'), A_843) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6213, c_10280])).
% 8.56/2.94  tff(c_10287, plain, (![A_843, B_844]: (r1_tarski('#skF_4', k2_zfmisc_1(A_843, B_844)) | ~r1_tarski('#skF_1', A_843))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_8690, c_10176, c_10282])).
% 8.56/2.94  tff(c_10481, plain, (![A_852]: (r1_tarski('#skF_4', '#skF_3') | ~r1_tarski('#skF_1', A_852))), inference(superposition, [status(thm), theory('equality')], [c_10470, c_10287])).
% 8.56/2.94  tff(c_10574, plain, (![A_854]: (~r1_tarski('#skF_1', A_854))), inference(negUnitSimplification, [status(thm)], [c_10138, c_10481])).
% 8.56/2.94  tff(c_10579, plain, $false, inference(resolution, [status(thm)], [c_6, c_10574])).
% 8.56/2.94  tff(c_10580, plain, (![A_280]: (r1_tarski('#skF_1', A_280))), inference(splitRight, [status(thm)], [c_8737])).
% 8.56/2.94  tff(c_10585, plain, (![A_855]: (r1_tarski('#skF_1', A_855))), inference(splitRight, [status(thm)], [c_8737])).
% 8.56/2.94  tff(c_10, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.56/2.94  tff(c_10641, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_10585, c_10])).
% 8.56/2.94  tff(c_10581, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_8737])).
% 8.56/2.94  tff(c_10691, plain, (r1_tarski('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10641, c_10581])).
% 8.56/2.94  tff(c_10693, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_10691, c_2])).
% 8.56/2.94  tff(c_10699, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10580, c_10693])).
% 8.56/2.94  tff(c_80, plain, (![A_40]: (k2_zfmisc_1(A_40, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.56/2.94  tff(c_84, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_80, c_32])).
% 8.56/2.94  tff(c_18, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.56/2.94  tff(c_2769, plain, (![A_276]: (v4_relat_1(k1_xboole_0, A_276))), inference(resolution, [status(thm)], [c_18, c_2749])).
% 8.56/2.94  tff(c_2805, plain, (![B_286, A_287]: (r1_tarski(k1_relat_1(B_286), A_287) | ~v4_relat_1(B_286, A_287) | ~v1_relat_1(B_286))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.56/2.94  tff(c_2836, plain, (![B_290]: (k1_relat_1(B_290)=k1_xboole_0 | ~v4_relat_1(B_290, k1_xboole_0) | ~v1_relat_1(B_290))), inference(resolution, [status(thm)], [c_2805, c_10])).
% 8.56/2.94  tff(c_2848, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2769, c_2836])).
% 8.56/2.94  tff(c_2855, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2848])).
% 8.56/2.94  tff(c_6321, plain, (![A_552, B_553]: (k1_relset_1(A_552, B_553, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_6304])).
% 8.56/2.94  tff(c_6325, plain, (![A_552, B_553]: (k1_relset_1(A_552, B_553, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2855, c_6321])).
% 8.56/2.94  tff(c_16, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.56/2.94  tff(c_48, plain, (![C_34, B_33]: (v1_funct_2(C_34, k1_xboole_0, B_33) | k1_relset_1(k1_xboole_0, B_33, C_34)!=k1_xboole_0 | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_33))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.56/2.94  tff(c_8458, plain, (![C_712, B_713]: (v1_funct_2(C_712, k1_xboole_0, B_713) | k1_relset_1(k1_xboole_0, B_713, C_712)!=k1_xboole_0 | ~m1_subset_1(C_712, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_48])).
% 8.56/2.94  tff(c_8464, plain, (![B_713]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_713) | k1_relset_1(k1_xboole_0, B_713, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_8458])).
% 8.56/2.94  tff(c_8468, plain, (![B_713]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_713))), inference(demodulation, [status(thm), theory('equality')], [c_6325, c_8464])).
% 8.56/2.94  tff(c_10646, plain, (![B_713]: (v1_funct_2('#skF_1', '#skF_1', B_713))), inference(demodulation, [status(thm), theory('equality')], [c_10641, c_10641, c_8468])).
% 8.56/2.94  tff(c_10957, plain, (![B_713]: (v1_funct_2('#skF_4', '#skF_4', B_713))), inference(demodulation, [status(thm), theory('equality')], [c_10699, c_10699, c_10646])).
% 8.56/2.94  tff(c_10715, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10699, c_147])).
% 8.56/2.94  tff(c_11024, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10957, c_10715])).
% 8.56/2.94  tff(c_11025, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_68])).
% 8.56/2.94  tff(c_11530, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_11510, c_11025])).
% 8.56/2.94  tff(c_11550, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11044, c_11336, c_11530])).
% 8.56/2.94  tff(c_11554, plain, (~v4_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_11550])).
% 8.56/2.94  tff(c_11558, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11044, c_11104, c_11554])).
% 8.56/2.94  tff(c_11559, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_58])).
% 8.56/2.94  tff(c_11561, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_11559, c_8])).
% 8.56/2.94  tff(c_11573, plain, (![B_6]: (k2_zfmisc_1('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11559, c_11559, c_16])).
% 8.56/2.94  tff(c_11560, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_58])).
% 8.56/2.94  tff(c_11566, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11559, c_11560])).
% 8.56/2.94  tff(c_11619, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11573, c_11566, c_62])).
% 8.56/2.94  tff(c_11623, plain, (![A_958, B_959]: (r1_tarski(A_958, B_959) | ~m1_subset_1(A_958, k1_zfmisc_1(B_959)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.56/2.94  tff(c_11634, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_11619, c_11623])).
% 8.56/2.94  tff(c_11651, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_11634, c_2])).
% 8.56/2.94  tff(c_11657, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11561, c_11651])).
% 8.56/2.94  tff(c_11583, plain, (![A_7]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_11559, c_18])).
% 8.56/2.94  tff(c_11665, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_11657, c_11583])).
% 8.56/2.94  tff(c_11667, plain, (![B_6]: (k2_zfmisc_1('#skF_4', B_6)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11657, c_11657, c_11573])).
% 8.56/2.94  tff(c_11812, plain, (![C_982, A_983, B_984]: (v4_relat_1(C_982, A_983) | ~m1_subset_1(C_982, k1_zfmisc_1(k2_zfmisc_1(A_983, B_984))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.56/2.94  tff(c_11854, plain, (![A_992, A_993, B_994]: (v4_relat_1(A_992, A_993) | ~r1_tarski(A_992, k2_zfmisc_1(A_993, B_994)))), inference(resolution, [status(thm)], [c_22, c_11812])).
% 8.56/2.94  tff(c_11871, plain, (![A_993, B_994]: (v4_relat_1(k2_zfmisc_1(A_993, B_994), A_993))), inference(resolution, [status(thm)], [c_6, c_11854])).
% 8.56/2.94  tff(c_11881, plain, (![B_997, A_998]: (r1_tarski(k1_relat_1(B_997), A_998) | ~v4_relat_1(B_997, A_998) | ~v1_relat_1(B_997))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.56/2.94  tff(c_11605, plain, (![A_4]: (A_4='#skF_1' | ~r1_tarski(A_4, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11559, c_11559, c_10])).
% 8.56/2.94  tff(c_11662, plain, (![A_4]: (A_4='#skF_4' | ~r1_tarski(A_4, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11657, c_11657, c_11605])).
% 8.56/2.94  tff(c_11931, plain, (![B_1004]: (k1_relat_1(B_1004)='#skF_4' | ~v4_relat_1(B_1004, '#skF_4') | ~v1_relat_1(B_1004))), inference(resolution, [status(thm)], [c_11881, c_11662])).
% 8.56/2.94  tff(c_11935, plain, (![B_994]: (k1_relat_1(k2_zfmisc_1('#skF_4', B_994))='#skF_4' | ~v1_relat_1(k2_zfmisc_1('#skF_4', B_994)))), inference(resolution, [status(thm)], [c_11871, c_11931])).
% 8.56/2.94  tff(c_11946, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_11667, c_11935])).
% 8.56/2.94  tff(c_12042, plain, (![A_1021, B_1022, C_1023]: (k1_relset_1(A_1021, B_1022, C_1023)=k1_relat_1(C_1023) | ~m1_subset_1(C_1023, k1_zfmisc_1(k2_zfmisc_1(A_1021, B_1022))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.56/2.94  tff(c_12049, plain, (![A_1021, B_1022]: (k1_relset_1(A_1021, B_1022, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_11665, c_12042])).
% 8.56/2.94  tff(c_12058, plain, (![A_1021, B_1022]: (k1_relset_1(A_1021, B_1022, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11946, c_12049])).
% 8.56/2.94  tff(c_11671, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11657, c_11559])).
% 8.56/2.94  tff(c_72, plain, (![C_34, B_33]: (v1_funct_2(C_34, k1_xboole_0, B_33) | k1_relset_1(k1_xboole_0, B_33, C_34)!=k1_xboole_0 | ~m1_subset_1(C_34, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_48])).
% 8.56/2.94  tff(c_12377, plain, (![C_1068, B_1069]: (v1_funct_2(C_1068, '#skF_4', B_1069) | k1_relset_1('#skF_4', B_1069, C_1068)!='#skF_4' | ~m1_subset_1(C_1068, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_11671, c_11671, c_11671, c_11671, c_72])).
% 8.56/2.94  tff(c_12380, plain, (![B_1069]: (v1_funct_2('#skF_4', '#skF_4', B_1069) | k1_relset_1('#skF_4', B_1069, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_11665, c_12377])).
% 8.56/2.94  tff(c_12386, plain, (![B_1069]: (v1_funct_2('#skF_4', '#skF_4', B_1069))), inference(demodulation, [status(thm), theory('equality')], [c_12058, c_12380])).
% 8.56/2.94  tff(c_11678, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11657, c_11657, c_68])).
% 8.56/2.94  tff(c_11679, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_11678])).
% 8.56/2.94  tff(c_12391, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12386, c_11679])).
% 8.56/2.94  tff(c_12392, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_11678])).
% 8.56/2.94  tff(c_12479, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11665, c_11667, c_12392])).
% 8.56/2.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.56/2.94  
% 8.56/2.94  Inference rules
% 8.56/2.94  ----------------------
% 8.56/2.94  #Ref     : 0
% 8.56/2.94  #Sup     : 2512
% 8.56/2.94  #Fact    : 0
% 8.56/2.94  #Define  : 0
% 8.56/2.94  #Split   : 44
% 8.56/2.94  #Chain   : 0
% 8.56/2.94  #Close   : 0
% 8.56/2.94  
% 8.56/2.94  Ordering : KBO
% 8.56/2.94  
% 8.56/2.94  Simplification rules
% 8.56/2.94  ----------------------
% 8.56/2.94  #Subsume      : 583
% 8.56/2.94  #Demod        : 3364
% 8.56/2.94  #Tautology    : 1156
% 8.56/2.94  #SimpNegUnit  : 105
% 8.56/2.94  #BackRed      : 527
% 8.56/2.94  
% 8.56/2.94  #Partial instantiations: 0
% 8.56/2.94  #Strategies tried      : 1
% 8.56/2.94  
% 8.56/2.94  Timing (in seconds)
% 8.56/2.94  ----------------------
% 8.56/2.94  Preprocessing        : 0.35
% 8.56/2.94  Parsing              : 0.19
% 8.56/2.94  CNF conversion       : 0.02
% 8.56/2.94  Main loop            : 1.81
% 8.56/2.94  Inferencing          : 0.59
% 8.56/2.94  Reduction            : 0.64
% 8.56/2.94  Demodulation         : 0.44
% 8.56/2.94  BG Simplification    : 0.06
% 8.56/2.94  Subsumption          : 0.38
% 8.56/2.94  Abstraction          : 0.09
% 8.56/2.94  MUC search           : 0.00
% 8.56/2.94  Cooper               : 0.00
% 8.56/2.94  Total                : 2.23
% 8.56/2.94  Index Insertion      : 0.00
% 8.56/2.94  Index Deletion       : 0.00
% 8.56/2.94  Index Matching       : 0.00
% 8.56/2.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
