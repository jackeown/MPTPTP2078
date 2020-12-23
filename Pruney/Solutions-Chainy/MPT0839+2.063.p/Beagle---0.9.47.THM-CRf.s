%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:30 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 125 expanded)
%              Number of leaves         :   39 (  59 expanded)
%              Depth                    :    7
%              Number of atoms          :  103 ( 225 expanded)
%              Number of equality atoms :   38 (  55 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_64,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_43,axiom,(
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

tff(f_55,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_40,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_20,plain,(
    ! [A_16,B_17] : v1_relat_1(k2_zfmisc_1(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_63,plain,(
    ! [B_54,A_55] :
      ( v1_relat_1(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55))
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_66,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_63])).

tff(c_69,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_66])).

tff(c_70,plain,(
    ! [A_56] :
      ( k1_relat_1(A_56) = k1_xboole_0
      | k2_relat_1(A_56) != k1_xboole_0
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_77,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_69,c_70])).

tff(c_79,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_77])).

tff(c_89,plain,(
    ! [A_59] :
      ( k2_relat_1(A_59) = k1_xboole_0
      | k1_relat_1(A_59) != k1_xboole_0
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_92,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_69,c_89])).

tff(c_98,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_92])).

tff(c_293,plain,(
    ! [A_98,B_99,C_100] :
      ( k1_relset_1(A_98,B_99,C_100) = k1_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_307,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_293])).

tff(c_111,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_1'(A_63,B_64),B_64)
      | r1_xboole_0(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_127,plain,(
    ! [A_67,B_68] :
      ( m1_subset_1('#skF_1'(A_67,B_68),B_68)
      | r1_xboole_0(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_111,c_16])).

tff(c_100,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_1'(A_60,B_61),A_60)
      | r1_xboole_0(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38,plain,(
    ! [D_43] :
      ( ~ r2_hidden(D_43,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_43,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_108,plain,(
    ! [B_61] :
      ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4'),B_61),'#skF_3')
      | r1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4'),B_61) ) ),
    inference(resolution,[status(thm)],[c_100,c_38])).

tff(c_136,plain,(
    r1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_127,c_108])).

tff(c_313,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_136])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_333,plain,(
    k4_xboole_0(k1_relat_1('#skF_4'),'#skF_3') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_313,c_10])).

tff(c_14,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_142,plain,(
    ! [C_69,A_70,B_71] :
      ( v4_relat_1(C_69,A_70)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_156,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_142])).

tff(c_22,plain,(
    ! [B_19,A_18] :
      ( k7_relat_1(B_19,A_18) = B_19
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_160,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_156,c_22])).

tff(c_163,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_160])).

tff(c_218,plain,(
    ! [B_82,A_83] :
      ( k3_xboole_0(k1_relat_1(B_82),A_83) = k1_relat_1(k7_relat_1(B_82,A_83))
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8,plain,(
    ! [A_6,B_7] : k5_xboole_0(A_6,k3_xboole_0(A_6,B_7)) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_411,plain,(
    ! [B_112,A_113] :
      ( k5_xboole_0(k1_relat_1(B_112),k1_relat_1(k7_relat_1(B_112,A_113))) = k4_xboole_0(k1_relat_1(B_112),A_113)
      | ~ v1_relat_1(B_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_8])).

tff(c_420,plain,
    ( k5_xboole_0(k1_relat_1('#skF_4'),k1_relat_1('#skF_4')) = k4_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_411])).

tff(c_424,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_333,c_14,c_420])).

tff(c_426,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_424])).

tff(c_428,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_77])).

tff(c_716,plain,(
    ! [A_154,B_155,C_156] :
      ( k2_relset_1(A_154,B_155,C_156) = k2_relat_1(C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_727,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_716])).

tff(c_731,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_727])).

tff(c_733,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_731])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n018.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 19:55:27 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.37  
% 2.59/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.37  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.59/1.37  
% 2.59/1.37  %Foreground sorts:
% 2.59/1.37  
% 2.59/1.37  
% 2.59/1.37  %Background operators:
% 2.59/1.37  
% 2.59/1.37  
% 2.59/1.37  %Foreground operators:
% 2.59/1.37  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.59/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.59/1.37  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.59/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.59/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.59/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.59/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.59/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.59/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.59/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.59/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.59/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.59/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.59/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.59/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.59/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.59/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.59/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.59/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.37  
% 2.89/1.38  tff(f_115, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 2.89/1.38  tff(f_64, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.89/1.38  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.89/1.38  tff(f_76, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 2.89/1.38  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.89/1.38  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.89/1.38  tff(f_55, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.89/1.38  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.89/1.38  tff(f_51, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.89/1.38  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.89/1.38  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.89/1.38  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.89/1.38  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.89/1.38  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.89/1.38  tff(c_40, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.89/1.38  tff(c_20, plain, (![A_16, B_17]: (v1_relat_1(k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.89/1.38  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.89/1.38  tff(c_63, plain, (![B_54, A_55]: (v1_relat_1(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.89/1.38  tff(c_66, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_63])).
% 2.89/1.38  tff(c_69, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_66])).
% 2.89/1.38  tff(c_70, plain, (![A_56]: (k1_relat_1(A_56)=k1_xboole_0 | k2_relat_1(A_56)!=k1_xboole_0 | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.89/1.38  tff(c_77, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_69, c_70])).
% 2.89/1.38  tff(c_79, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_77])).
% 2.89/1.38  tff(c_89, plain, (![A_59]: (k2_relat_1(A_59)=k1_xboole_0 | k1_relat_1(A_59)!=k1_xboole_0 | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.89/1.38  tff(c_92, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_69, c_89])).
% 2.89/1.38  tff(c_98, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_79, c_92])).
% 2.89/1.38  tff(c_293, plain, (![A_98, B_99, C_100]: (k1_relset_1(A_98, B_99, C_100)=k1_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.89/1.38  tff(c_307, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_293])).
% 2.89/1.38  tff(c_111, plain, (![A_63, B_64]: (r2_hidden('#skF_1'(A_63, B_64), B_64) | r1_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.89/1.38  tff(c_16, plain, (![A_11, B_12]: (m1_subset_1(A_11, B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.89/1.38  tff(c_127, plain, (![A_67, B_68]: (m1_subset_1('#skF_1'(A_67, B_68), B_68) | r1_xboole_0(A_67, B_68))), inference(resolution, [status(thm)], [c_111, c_16])).
% 2.89/1.38  tff(c_100, plain, (![A_60, B_61]: (r2_hidden('#skF_1'(A_60, B_61), A_60) | r1_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.89/1.38  tff(c_38, plain, (![D_43]: (~r2_hidden(D_43, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_43, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.89/1.38  tff(c_108, plain, (![B_61]: (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4'), B_61), '#skF_3') | r1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4'), B_61))), inference(resolution, [status(thm)], [c_100, c_38])).
% 2.89/1.38  tff(c_136, plain, (r1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_127, c_108])).
% 2.89/1.38  tff(c_313, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_307, c_136])).
% 2.89/1.38  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.89/1.38  tff(c_333, plain, (k4_xboole_0(k1_relat_1('#skF_4'), '#skF_3')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_313, c_10])).
% 2.89/1.38  tff(c_14, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.89/1.38  tff(c_142, plain, (![C_69, A_70, B_71]: (v4_relat_1(C_69, A_70) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.89/1.38  tff(c_156, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_142])).
% 2.89/1.38  tff(c_22, plain, (![B_19, A_18]: (k7_relat_1(B_19, A_18)=B_19 | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.89/1.38  tff(c_160, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_156, c_22])).
% 2.89/1.38  tff(c_163, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_69, c_160])).
% 2.89/1.38  tff(c_218, plain, (![B_82, A_83]: (k3_xboole_0(k1_relat_1(B_82), A_83)=k1_relat_1(k7_relat_1(B_82, A_83)) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.89/1.38  tff(c_8, plain, (![A_6, B_7]: (k5_xboole_0(A_6, k3_xboole_0(A_6, B_7))=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.89/1.38  tff(c_411, plain, (![B_112, A_113]: (k5_xboole_0(k1_relat_1(B_112), k1_relat_1(k7_relat_1(B_112, A_113)))=k4_xboole_0(k1_relat_1(B_112), A_113) | ~v1_relat_1(B_112))), inference(superposition, [status(thm), theory('equality')], [c_218, c_8])).
% 2.89/1.38  tff(c_420, plain, (k5_xboole_0(k1_relat_1('#skF_4'), k1_relat_1('#skF_4'))=k4_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_163, c_411])).
% 2.89/1.38  tff(c_424, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_69, c_333, c_14, c_420])).
% 2.89/1.38  tff(c_426, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_424])).
% 2.89/1.38  tff(c_428, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_77])).
% 2.89/1.38  tff(c_716, plain, (![A_154, B_155, C_156]: (k2_relset_1(A_154, B_155, C_156)=k2_relat_1(C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.89/1.38  tff(c_727, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_716])).
% 2.89/1.38  tff(c_731, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_428, c_727])).
% 2.89/1.38  tff(c_733, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_731])).
% 2.89/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.38  
% 2.89/1.38  Inference rules
% 2.89/1.38  ----------------------
% 2.89/1.38  #Ref     : 0
% 2.89/1.38  #Sup     : 155
% 2.89/1.38  #Fact    : 0
% 2.89/1.38  #Define  : 0
% 2.89/1.38  #Split   : 1
% 2.89/1.38  #Chain   : 0
% 2.89/1.38  #Close   : 0
% 2.89/1.38  
% 2.89/1.38  Ordering : KBO
% 2.89/1.38  
% 2.89/1.38  Simplification rules
% 2.89/1.38  ----------------------
% 2.89/1.38  #Subsume      : 9
% 2.89/1.38  #Demod        : 45
% 2.89/1.38  #Tautology    : 63
% 2.89/1.38  #SimpNegUnit  : 3
% 2.89/1.38  #BackRed      : 17
% 2.89/1.38  
% 2.89/1.38  #Partial instantiations: 0
% 2.89/1.38  #Strategies tried      : 1
% 2.89/1.38  
% 2.89/1.38  Timing (in seconds)
% 2.89/1.38  ----------------------
% 2.89/1.39  Preprocessing        : 0.31
% 2.89/1.39  Parsing              : 0.17
% 2.89/1.39  CNF conversion       : 0.02
% 2.89/1.39  Main loop            : 0.32
% 2.89/1.39  Inferencing          : 0.13
% 2.89/1.39  Reduction            : 0.09
% 2.89/1.39  Demodulation         : 0.06
% 2.89/1.39  BG Simplification    : 0.02
% 2.89/1.39  Subsumption          : 0.05
% 2.89/1.39  Abstraction          : 0.02
% 2.89/1.39  MUC search           : 0.00
% 2.89/1.39  Cooper               : 0.00
% 2.89/1.39  Total                : 0.66
% 2.89/1.39  Index Insertion      : 0.00
% 2.89/1.39  Index Deletion       : 0.00
% 2.89/1.39  Index Matching       : 0.00
% 2.89/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
