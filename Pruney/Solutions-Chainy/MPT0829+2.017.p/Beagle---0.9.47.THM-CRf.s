%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:23 EST 2020

% Result     : Theorem 13.53s
% Output     : CNFRefutation 13.53s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 543 expanded)
%              Number of leaves         :   34 ( 196 expanded)
%              Depth                    :   21
%              Number of atoms          :  207 (1087 expanded)
%              Number of equality atoms :   38 ( 172 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( r1_tarski(B,k1_relset_1(A,B,C))
            & B = k2_relset_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_68,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(c_24,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_18226,plain,(
    ! [B_593,A_594] :
      ( v1_relat_1(B_593)
      | ~ m1_subset_1(B_593,k1_zfmisc_1(A_594))
      | ~ v1_relat_1(A_594) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18232,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_18226])).

tff(c_18236,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18232])).

tff(c_18472,plain,(
    ! [C_622,B_623,A_624] :
      ( v5_relat_1(C_622,B_623)
      | ~ m1_subset_1(C_622,k1_zfmisc_1(k2_zfmisc_1(A_624,B_623))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18481,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_18472])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k2_relat_1(B_16),A_15)
      | ~ v5_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18665,plain,(
    ! [A_646,B_647,C_648] :
      ( k2_relset_1(A_646,B_647,C_648) = k2_relat_1(C_648)
      | ~ m1_subset_1(C_648,k1_zfmisc_1(k2_zfmisc_1(A_646,B_647))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_18674,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_18665])).

tff(c_585,plain,(
    ! [A_104,B_105,C_106] :
      ( k1_relset_1(A_104,B_105,C_106) = k1_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_594,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_585])).

tff(c_42,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_119,plain,(
    ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_595,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_119])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_175,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_181,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_175])).

tff(c_185,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_181])).

tff(c_389,plain,(
    ! [C_77,B_78,A_79] :
      ( v5_relat_1(C_77,B_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_398,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_389])).

tff(c_44,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_212,plain,(
    ! [A_54,B_55] :
      ( v1_relat_1(A_54)
      | ~ v1_relat_1(B_55)
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_16,c_175])).

tff(c_221,plain,
    ( v1_relat_1(k6_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_212])).

tff(c_231,plain,(
    v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_221])).

tff(c_26,plain,(
    ! [A_19] :
      ( r1_tarski(A_19,k2_zfmisc_1(k1_relat_1(A_19),k2_relat_1(A_19)))
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_101,plain,(
    ! [A_40,B_41] :
      ( k2_xboole_0(A_40,B_41) = B_41
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_109,plain,(
    ! [B_4] : k2_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_101])).

tff(c_186,plain,(
    ! [A_51,C_52,B_53] :
      ( r1_tarski(A_51,k2_xboole_0(C_52,B_53))
      | ~ r1_tarski(A_51,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,B_9) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1256,plain,(
    ! [A_144,C_145,B_146] :
      ( k2_xboole_0(A_144,k2_xboole_0(C_145,B_146)) = k2_xboole_0(C_145,B_146)
      | ~ r1_tarski(A_144,B_146) ) ),
    inference(resolution,[status(thm)],[c_186,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_209,plain,(
    ! [A_51,A_1,B_2] :
      ( r1_tarski(A_51,k2_xboole_0(A_1,B_2))
      | ~ r1_tarski(A_51,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_186])).

tff(c_3223,plain,(
    ! [A_243,C_244,B_245,A_246] :
      ( r1_tarski(A_243,k2_xboole_0(C_244,B_245))
      | ~ r1_tarski(A_243,A_246)
      | ~ r1_tarski(A_246,B_245) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1256,c_209])).

tff(c_3565,plain,(
    ! [C_250,B_251] :
      ( r1_tarski(k6_relat_1('#skF_2'),k2_xboole_0(C_250,B_251))
      | ~ r1_tarski('#skF_3',B_251) ) ),
    inference(resolution,[status(thm)],[c_44,c_3223])).

tff(c_3752,plain,(
    ! [B_258] :
      ( r1_tarski(k6_relat_1('#skF_2'),B_258)
      | ~ r1_tarski('#skF_3',B_258) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_3565])).

tff(c_397,plain,(
    ! [A_10,B_78,A_79] :
      ( v5_relat_1(A_10,B_78)
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_79,B_78)) ) ),
    inference(resolution,[status(thm)],[c_16,c_389])).

tff(c_6711,plain,(
    ! [B_315,A_316] :
      ( v5_relat_1(k6_relat_1('#skF_2'),B_315)
      | ~ r1_tarski('#skF_3',k2_zfmisc_1(A_316,B_315)) ) ),
    inference(resolution,[status(thm)],[c_3752,c_397])).

tff(c_6720,plain,
    ( v5_relat_1(k6_relat_1('#skF_2'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_6711])).

tff(c_6732,plain,(
    v5_relat_1(k6_relat_1('#skF_2'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_6720])).

tff(c_30,plain,(
    ! [A_20] : k2_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_297,plain,(
    ! [B_62,A_63] :
      ( r1_tarski(k2_relat_1(B_62),A_63)
      | ~ v5_relat_1(B_62,A_63)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_316,plain,(
    ! [A_20,A_63] :
      ( r1_tarski(A_20,A_63)
      | ~ v5_relat_1(k6_relat_1(A_20),A_63)
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_297])).

tff(c_6742,plain,
    ( r1_tarski('#skF_2',k2_relat_1('#skF_3'))
    | ~ v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6732,c_316])).

tff(c_6749,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_6742])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_320,plain,(
    ! [B_62,A_63] :
      ( k2_relat_1(B_62) = A_63
      | ~ r1_tarski(A_63,k2_relat_1(B_62))
      | ~ v5_relat_1(B_62,A_63)
      | ~ v1_relat_1(B_62) ) ),
    inference(resolution,[status(thm)],[c_297,c_4])).

tff(c_6796,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6749,c_320])).

tff(c_6811,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_398,c_6796])).

tff(c_326,plain,(
    ! [A_65] :
      ( r1_tarski(A_65,k2_zfmisc_1(k1_relat_1(A_65),k2_relat_1(A_65)))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_345,plain,(
    ! [A_65] :
      ( k2_xboole_0(A_65,k2_zfmisc_1(k1_relat_1(A_65),k2_relat_1(A_65))) = k2_zfmisc_1(k1_relat_1(A_65),k2_relat_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(resolution,[status(thm)],[c_326,c_12])).

tff(c_6977,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) = k2_xboole_0('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6811,c_345])).

tff(c_7031,plain,(
    k2_xboole_0('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) = k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_6811,c_6977])).

tff(c_3646,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(k6_relat_1('#skF_2'),k2_xboole_0(A_1,B_2))
      | ~ r1_tarski('#skF_3',A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3565])).

tff(c_18023,plain,
    ( r1_tarski(k6_relat_1('#skF_2'),k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7031,c_3646])).

tff(c_18091,plain,(
    r1_tarski(k6_relat_1('#skF_2'),k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18023])).

tff(c_28,plain,(
    ! [A_20] : k1_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_593,plain,(
    ! [A_104,B_105,A_10] :
      ( k1_relset_1(A_104,B_105,A_10) = k1_relat_1(A_10)
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_104,B_105)) ) ),
    inference(resolution,[status(thm)],[c_16,c_585])).

tff(c_18122,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2',k6_relat_1('#skF_2')) = k1_relat_1(k6_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_18091,c_593])).

tff(c_18148,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2',k6_relat_1('#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_18122])).

tff(c_702,plain,(
    ! [A_113,B_114,C_115] :
      ( m1_subset_1(k1_relset_1(A_113,B_114,C_115),k1_zfmisc_1(A_113))
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2052,plain,(
    ! [A_180,B_181,C_182] :
      ( r1_tarski(k1_relset_1(A_180,B_181,C_182),A_180)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181))) ) ),
    inference(resolution,[status(thm)],[c_702,c_14])).

tff(c_2066,plain,(
    ! [A_180,B_181,A_10] :
      ( r1_tarski(k1_relset_1(A_180,B_181,A_10),A_180)
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_180,B_181)) ) ),
    inference(resolution,[status(thm)],[c_16,c_2052])).

tff(c_18173,plain,
    ( r1_tarski('#skF_2',k1_relat_1('#skF_3'))
    | ~ r1_tarski(k6_relat_1('#skF_2'),k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18148,c_2066])).

tff(c_18180,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18091,c_18173])).

tff(c_18182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_595,c_18180])).

tff(c_18183,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_18675,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18674,c_18183])).

tff(c_18241,plain,(
    ! [A_595,B_596] :
      ( v1_relat_1(A_595)
      | ~ v1_relat_1(B_596)
      | ~ r1_tarski(A_595,B_596) ) ),
    inference(resolution,[status(thm)],[c_16,c_18226])).

tff(c_18250,plain,
    ( v1_relat_1(k6_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_18241])).

tff(c_18260,plain,(
    v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18236,c_18250])).

tff(c_18279,plain,(
    ! [A_599,C_600,B_601] :
      ( r1_tarski(A_599,k2_xboole_0(C_600,B_601))
      | ~ r1_tarski(A_599,B_601) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_19434,plain,(
    ! [A_679,C_680,B_681] :
      ( k2_xboole_0(A_679,k2_xboole_0(C_680,B_681)) = k2_xboole_0(C_680,B_681)
      | ~ r1_tarski(A_679,B_681) ) ),
    inference(resolution,[status(thm)],[c_18279,c_12])).

tff(c_18302,plain,(
    ! [A_599,B_2,A_1] :
      ( r1_tarski(A_599,k2_xboole_0(B_2,A_1))
      | ~ r1_tarski(A_599,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_18279])).

tff(c_23073,plain,(
    ! [A_828,C_829,B_830,A_831] :
      ( r1_tarski(A_828,k2_xboole_0(C_829,B_830))
      | ~ r1_tarski(A_828,A_831)
      | ~ r1_tarski(A_831,B_830) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19434,c_18302])).

tff(c_23498,plain,(
    ! [C_835,B_836] :
      ( r1_tarski(k6_relat_1('#skF_2'),k2_xboole_0(C_835,B_836))
      | ~ r1_tarski('#skF_3',B_836) ) ),
    inference(resolution,[status(thm)],[c_44,c_23073])).

tff(c_23723,plain,(
    ! [B_839] :
      ( r1_tarski(k6_relat_1('#skF_2'),B_839)
      | ~ r1_tarski('#skF_3',B_839) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_23498])).

tff(c_18480,plain,(
    ! [A_10,B_623,A_624] :
      ( v5_relat_1(A_10,B_623)
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_624,B_623)) ) ),
    inference(resolution,[status(thm)],[c_16,c_18472])).

tff(c_34148,plain,(
    ! [B_1016,A_1017] :
      ( v5_relat_1(k6_relat_1('#skF_2'),B_1016)
      | ~ r1_tarski('#skF_3',k2_zfmisc_1(A_1017,B_1016)) ) ),
    inference(resolution,[status(thm)],[c_23723,c_18480])).

tff(c_34160,plain,
    ( v5_relat_1(k6_relat_1('#skF_2'),k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_34148])).

tff(c_34173,plain,(
    v5_relat_1(k6_relat_1('#skF_2'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18236,c_34160])).

tff(c_18442,plain,(
    ! [B_620,A_621] :
      ( r1_tarski(k2_relat_1(B_620),A_621)
      | ~ v5_relat_1(B_620,A_621)
      | ~ v1_relat_1(B_620) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20189,plain,(
    ! [B_720,A_721] :
      ( k2_relat_1(B_720) = A_721
      | ~ r1_tarski(A_721,k2_relat_1(B_720))
      | ~ v5_relat_1(B_720,A_721)
      | ~ v1_relat_1(B_720) ) ),
    inference(resolution,[status(thm)],[c_18442,c_4])).

tff(c_20196,plain,(
    ! [A_20,A_721] :
      ( k2_relat_1(k6_relat_1(A_20)) = A_721
      | ~ r1_tarski(A_721,A_20)
      | ~ v5_relat_1(k6_relat_1(A_20),A_721)
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_20189])).

tff(c_20202,plain,(
    ! [A_721,A_20] :
      ( A_721 = A_20
      | ~ r1_tarski(A_721,A_20)
      | ~ v5_relat_1(k6_relat_1(A_20),A_721)
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_20196])).

tff(c_34181,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_34173,c_20202])).

tff(c_34192,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18260,c_34181])).

tff(c_34193,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_18675,c_34192])).

tff(c_34421,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_34193])).

tff(c_34425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18236,c_18481,c_34421])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:37:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.53/6.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.53/6.20  
% 13.53/6.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.53/6.20  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 13.53/6.20  
% 13.53/6.20  %Foreground sorts:
% 13.53/6.20  
% 13.53/6.20  
% 13.53/6.20  %Background operators:
% 13.53/6.20  
% 13.53/6.20  
% 13.53/6.20  %Foreground operators:
% 13.53/6.20  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 13.53/6.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.53/6.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.53/6.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.53/6.20  tff('#skF_2', type, '#skF_2': $i).
% 13.53/6.20  tff('#skF_3', type, '#skF_3': $i).
% 13.53/6.20  tff('#skF_1', type, '#skF_1': $i).
% 13.53/6.20  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 13.53/6.20  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 13.53/6.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.53/6.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.53/6.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.53/6.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.53/6.20  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 13.53/6.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.53/6.20  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 13.53/6.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.53/6.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.53/6.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.53/6.20  
% 13.53/6.22  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 13.53/6.22  tff(f_95, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(B), C) => (r1_tarski(B, k1_relset_1(A, B, C)) & (B = k2_relset_1(A, B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_relset_1)).
% 13.53/6.22  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 13.53/6.22  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 13.53/6.22  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 13.53/6.22  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 13.53/6.22  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 13.53/6.22  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.53/6.22  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 13.53/6.22  tff(f_64, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 13.53/6.22  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 13.53/6.22  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 13.53/6.22  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 13.53/6.22  tff(f_68, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 13.53/6.22  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 13.53/6.22  tff(c_24, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.53/6.22  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.53/6.22  tff(c_18226, plain, (![B_593, A_594]: (v1_relat_1(B_593) | ~m1_subset_1(B_593, k1_zfmisc_1(A_594)) | ~v1_relat_1(A_594))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.53/6.22  tff(c_18232, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_18226])).
% 13.53/6.22  tff(c_18236, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_18232])).
% 13.53/6.22  tff(c_18472, plain, (![C_622, B_623, A_624]: (v5_relat_1(C_622, B_623) | ~m1_subset_1(C_622, k1_zfmisc_1(k2_zfmisc_1(A_624, B_623))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.53/6.22  tff(c_18481, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_18472])).
% 13.53/6.22  tff(c_22, plain, (![B_16, A_15]: (r1_tarski(k2_relat_1(B_16), A_15) | ~v5_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 13.53/6.22  tff(c_18665, plain, (![A_646, B_647, C_648]: (k2_relset_1(A_646, B_647, C_648)=k2_relat_1(C_648) | ~m1_subset_1(C_648, k1_zfmisc_1(k2_zfmisc_1(A_646, B_647))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.53/6.22  tff(c_18674, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_18665])).
% 13.53/6.22  tff(c_585, plain, (![A_104, B_105, C_106]: (k1_relset_1(A_104, B_105, C_106)=k1_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 13.53/6.22  tff(c_594, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_585])).
% 13.53/6.22  tff(c_42, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.53/6.22  tff(c_119, plain, (~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_42])).
% 13.53/6.22  tff(c_595, plain, (~r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_594, c_119])).
% 13.53/6.22  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.53/6.22  tff(c_175, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.53/6.22  tff(c_181, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_175])).
% 13.53/6.22  tff(c_185, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_181])).
% 13.53/6.22  tff(c_389, plain, (![C_77, B_78, A_79]: (v5_relat_1(C_77, B_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.53/6.22  tff(c_398, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_389])).
% 13.53/6.22  tff(c_44, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.53/6.22  tff(c_16, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.53/6.22  tff(c_212, plain, (![A_54, B_55]: (v1_relat_1(A_54) | ~v1_relat_1(B_55) | ~r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_16, c_175])).
% 13.53/6.22  tff(c_221, plain, (v1_relat_1(k6_relat_1('#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_212])).
% 13.53/6.22  tff(c_231, plain, (v1_relat_1(k6_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_221])).
% 13.53/6.22  tff(c_26, plain, (![A_19]: (r1_tarski(A_19, k2_zfmisc_1(k1_relat_1(A_19), k2_relat_1(A_19))) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.53/6.22  tff(c_101, plain, (![A_40, B_41]: (k2_xboole_0(A_40, B_41)=B_41 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.53/6.22  tff(c_109, plain, (![B_4]: (k2_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_101])).
% 13.53/6.22  tff(c_186, plain, (![A_51, C_52, B_53]: (r1_tarski(A_51, k2_xboole_0(C_52, B_53)) | ~r1_tarski(A_51, B_53))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.53/6.22  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(A_8, B_9)=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.53/6.22  tff(c_1256, plain, (![A_144, C_145, B_146]: (k2_xboole_0(A_144, k2_xboole_0(C_145, B_146))=k2_xboole_0(C_145, B_146) | ~r1_tarski(A_144, B_146))), inference(resolution, [status(thm)], [c_186, c_12])).
% 13.53/6.22  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.53/6.22  tff(c_209, plain, (![A_51, A_1, B_2]: (r1_tarski(A_51, k2_xboole_0(A_1, B_2)) | ~r1_tarski(A_51, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_186])).
% 13.53/6.22  tff(c_3223, plain, (![A_243, C_244, B_245, A_246]: (r1_tarski(A_243, k2_xboole_0(C_244, B_245)) | ~r1_tarski(A_243, A_246) | ~r1_tarski(A_246, B_245))), inference(superposition, [status(thm), theory('equality')], [c_1256, c_209])).
% 13.53/6.22  tff(c_3565, plain, (![C_250, B_251]: (r1_tarski(k6_relat_1('#skF_2'), k2_xboole_0(C_250, B_251)) | ~r1_tarski('#skF_3', B_251))), inference(resolution, [status(thm)], [c_44, c_3223])).
% 13.53/6.22  tff(c_3752, plain, (![B_258]: (r1_tarski(k6_relat_1('#skF_2'), B_258) | ~r1_tarski('#skF_3', B_258))), inference(superposition, [status(thm), theory('equality')], [c_109, c_3565])).
% 13.53/6.22  tff(c_397, plain, (![A_10, B_78, A_79]: (v5_relat_1(A_10, B_78) | ~r1_tarski(A_10, k2_zfmisc_1(A_79, B_78)))), inference(resolution, [status(thm)], [c_16, c_389])).
% 13.53/6.22  tff(c_6711, plain, (![B_315, A_316]: (v5_relat_1(k6_relat_1('#skF_2'), B_315) | ~r1_tarski('#skF_3', k2_zfmisc_1(A_316, B_315)))), inference(resolution, [status(thm)], [c_3752, c_397])).
% 13.53/6.22  tff(c_6720, plain, (v5_relat_1(k6_relat_1('#skF_2'), k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_6711])).
% 13.53/6.22  tff(c_6732, plain, (v5_relat_1(k6_relat_1('#skF_2'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_6720])).
% 13.53/6.22  tff(c_30, plain, (![A_20]: (k2_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.53/6.22  tff(c_297, plain, (![B_62, A_63]: (r1_tarski(k2_relat_1(B_62), A_63) | ~v5_relat_1(B_62, A_63) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_58])).
% 13.53/6.22  tff(c_316, plain, (![A_20, A_63]: (r1_tarski(A_20, A_63) | ~v5_relat_1(k6_relat_1(A_20), A_63) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_297])).
% 13.53/6.22  tff(c_6742, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3')) | ~v1_relat_1(k6_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_6732, c_316])).
% 13.53/6.22  tff(c_6749, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_6742])).
% 13.53/6.22  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.53/6.22  tff(c_320, plain, (![B_62, A_63]: (k2_relat_1(B_62)=A_63 | ~r1_tarski(A_63, k2_relat_1(B_62)) | ~v5_relat_1(B_62, A_63) | ~v1_relat_1(B_62))), inference(resolution, [status(thm)], [c_297, c_4])).
% 13.53/6.22  tff(c_6796, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6749, c_320])).
% 13.53/6.22  tff(c_6811, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_185, c_398, c_6796])).
% 13.53/6.22  tff(c_326, plain, (![A_65]: (r1_tarski(A_65, k2_zfmisc_1(k1_relat_1(A_65), k2_relat_1(A_65))) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.53/6.22  tff(c_345, plain, (![A_65]: (k2_xboole_0(A_65, k2_zfmisc_1(k1_relat_1(A_65), k2_relat_1(A_65)))=k2_zfmisc_1(k1_relat_1(A_65), k2_relat_1(A_65)) | ~v1_relat_1(A_65))), inference(resolution, [status(thm)], [c_326, c_12])).
% 13.53/6.22  tff(c_6977, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))=k2_xboole_0('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6811, c_345])).
% 13.53/6.22  tff(c_7031, plain, (k2_xboole_0('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))=k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_6811, c_6977])).
% 13.53/6.22  tff(c_3646, plain, (![A_1, B_2]: (r1_tarski(k6_relat_1('#skF_2'), k2_xboole_0(A_1, B_2)) | ~r1_tarski('#skF_3', A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3565])).
% 13.53/6.22  tff(c_18023, plain, (r1_tarski(k6_relat_1('#skF_2'), k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')) | ~r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7031, c_3646])).
% 13.53/6.22  tff(c_18091, plain, (r1_tarski(k6_relat_1('#skF_2'), k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18023])).
% 13.53/6.22  tff(c_28, plain, (![A_20]: (k1_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.53/6.22  tff(c_593, plain, (![A_104, B_105, A_10]: (k1_relset_1(A_104, B_105, A_10)=k1_relat_1(A_10) | ~r1_tarski(A_10, k2_zfmisc_1(A_104, B_105)))), inference(resolution, [status(thm)], [c_16, c_585])).
% 13.53/6.22  tff(c_18122, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', k6_relat_1('#skF_2'))=k1_relat_1(k6_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_18091, c_593])).
% 13.53/6.22  tff(c_18148, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', k6_relat_1('#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_18122])).
% 13.53/6.22  tff(c_702, plain, (![A_113, B_114, C_115]: (m1_subset_1(k1_relset_1(A_113, B_114, C_115), k1_zfmisc_1(A_113)) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 13.53/6.22  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.53/6.22  tff(c_2052, plain, (![A_180, B_181, C_182]: (r1_tarski(k1_relset_1(A_180, B_181, C_182), A_180) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))))), inference(resolution, [status(thm)], [c_702, c_14])).
% 13.53/6.22  tff(c_2066, plain, (![A_180, B_181, A_10]: (r1_tarski(k1_relset_1(A_180, B_181, A_10), A_180) | ~r1_tarski(A_10, k2_zfmisc_1(A_180, B_181)))), inference(resolution, [status(thm)], [c_16, c_2052])).
% 13.53/6.22  tff(c_18173, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3')) | ~r1_tarski(k6_relat_1('#skF_2'), k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_18148, c_2066])).
% 13.53/6.22  tff(c_18180, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18091, c_18173])).
% 13.53/6.22  tff(c_18182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_595, c_18180])).
% 13.53/6.22  tff(c_18183, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(splitRight, [status(thm)], [c_42])).
% 13.53/6.22  tff(c_18675, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18674, c_18183])).
% 13.53/6.22  tff(c_18241, plain, (![A_595, B_596]: (v1_relat_1(A_595) | ~v1_relat_1(B_596) | ~r1_tarski(A_595, B_596))), inference(resolution, [status(thm)], [c_16, c_18226])).
% 13.53/6.22  tff(c_18250, plain, (v1_relat_1(k6_relat_1('#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_18241])).
% 13.53/6.22  tff(c_18260, plain, (v1_relat_1(k6_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18236, c_18250])).
% 13.53/6.22  tff(c_18279, plain, (![A_599, C_600, B_601]: (r1_tarski(A_599, k2_xboole_0(C_600, B_601)) | ~r1_tarski(A_599, B_601))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.53/6.22  tff(c_19434, plain, (![A_679, C_680, B_681]: (k2_xboole_0(A_679, k2_xboole_0(C_680, B_681))=k2_xboole_0(C_680, B_681) | ~r1_tarski(A_679, B_681))), inference(resolution, [status(thm)], [c_18279, c_12])).
% 13.53/6.22  tff(c_18302, plain, (![A_599, B_2, A_1]: (r1_tarski(A_599, k2_xboole_0(B_2, A_1)) | ~r1_tarski(A_599, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_18279])).
% 13.53/6.22  tff(c_23073, plain, (![A_828, C_829, B_830, A_831]: (r1_tarski(A_828, k2_xboole_0(C_829, B_830)) | ~r1_tarski(A_828, A_831) | ~r1_tarski(A_831, B_830))), inference(superposition, [status(thm), theory('equality')], [c_19434, c_18302])).
% 13.53/6.22  tff(c_23498, plain, (![C_835, B_836]: (r1_tarski(k6_relat_1('#skF_2'), k2_xboole_0(C_835, B_836)) | ~r1_tarski('#skF_3', B_836))), inference(resolution, [status(thm)], [c_44, c_23073])).
% 13.53/6.22  tff(c_23723, plain, (![B_839]: (r1_tarski(k6_relat_1('#skF_2'), B_839) | ~r1_tarski('#skF_3', B_839))), inference(superposition, [status(thm), theory('equality')], [c_109, c_23498])).
% 13.53/6.22  tff(c_18480, plain, (![A_10, B_623, A_624]: (v5_relat_1(A_10, B_623) | ~r1_tarski(A_10, k2_zfmisc_1(A_624, B_623)))), inference(resolution, [status(thm)], [c_16, c_18472])).
% 13.53/6.22  tff(c_34148, plain, (![B_1016, A_1017]: (v5_relat_1(k6_relat_1('#skF_2'), B_1016) | ~r1_tarski('#skF_3', k2_zfmisc_1(A_1017, B_1016)))), inference(resolution, [status(thm)], [c_23723, c_18480])).
% 13.53/6.22  tff(c_34160, plain, (v5_relat_1(k6_relat_1('#skF_2'), k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_34148])).
% 13.53/6.22  tff(c_34173, plain, (v5_relat_1(k6_relat_1('#skF_2'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18236, c_34160])).
% 13.53/6.22  tff(c_18442, plain, (![B_620, A_621]: (r1_tarski(k2_relat_1(B_620), A_621) | ~v5_relat_1(B_620, A_621) | ~v1_relat_1(B_620))), inference(cnfTransformation, [status(thm)], [f_58])).
% 13.53/6.22  tff(c_20189, plain, (![B_720, A_721]: (k2_relat_1(B_720)=A_721 | ~r1_tarski(A_721, k2_relat_1(B_720)) | ~v5_relat_1(B_720, A_721) | ~v1_relat_1(B_720))), inference(resolution, [status(thm)], [c_18442, c_4])).
% 13.53/6.22  tff(c_20196, plain, (![A_20, A_721]: (k2_relat_1(k6_relat_1(A_20))=A_721 | ~r1_tarski(A_721, A_20) | ~v5_relat_1(k6_relat_1(A_20), A_721) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_20189])).
% 13.53/6.22  tff(c_20202, plain, (![A_721, A_20]: (A_721=A_20 | ~r1_tarski(A_721, A_20) | ~v5_relat_1(k6_relat_1(A_20), A_721) | ~v1_relat_1(k6_relat_1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_20196])).
% 13.53/6.22  tff(c_34181, plain, (k2_relat_1('#skF_3')='#skF_2' | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v1_relat_1(k6_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_34173, c_20202])).
% 13.53/6.22  tff(c_34192, plain, (k2_relat_1('#skF_3')='#skF_2' | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18260, c_34181])).
% 13.53/6.22  tff(c_34193, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_18675, c_34192])).
% 13.53/6.22  tff(c_34421, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_34193])).
% 13.53/6.22  tff(c_34425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18236, c_18481, c_34421])).
% 13.53/6.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.53/6.22  
% 13.53/6.22  Inference rules
% 13.53/6.22  ----------------------
% 13.53/6.22  #Ref     : 0
% 13.53/6.22  #Sup     : 8472
% 13.53/6.22  #Fact    : 0
% 13.53/6.22  #Define  : 0
% 13.53/6.22  #Split   : 42
% 13.53/6.22  #Chain   : 0
% 13.53/6.22  #Close   : 0
% 13.53/6.22  
% 13.53/6.22  Ordering : KBO
% 13.53/6.22  
% 13.53/6.22  Simplification rules
% 13.53/6.22  ----------------------
% 13.53/6.22  #Subsume      : 3798
% 13.53/6.22  #Demod        : 4226
% 13.53/6.22  #Tautology    : 1568
% 13.53/6.22  #SimpNegUnit  : 137
% 13.53/6.22  #BackRed      : 11
% 13.53/6.22  
% 13.53/6.22  #Partial instantiations: 0
% 13.53/6.22  #Strategies tried      : 1
% 13.53/6.22  
% 13.53/6.22  Timing (in seconds)
% 13.53/6.22  ----------------------
% 13.53/6.22  Preprocessing        : 0.32
% 13.53/6.22  Parsing              : 0.17
% 13.53/6.22  CNF conversion       : 0.02
% 13.53/6.22  Main loop            : 5.12
% 13.53/6.22  Inferencing          : 1.06
% 13.53/6.22  Reduction            : 2.25
% 13.53/6.22  Demodulation         : 1.76
% 13.53/6.22  BG Simplification    : 0.09
% 13.53/6.22  Subsumption          : 1.45
% 13.53/6.22  Abstraction          : 0.15
% 13.53/6.22  MUC search           : 0.00
% 13.53/6.22  Cooper               : 0.00
% 13.53/6.22  Total                : 5.48
% 13.53/6.22  Index Insertion      : 0.00
% 13.53/6.22  Index Deletion       : 0.00
% 13.53/6.22  Index Matching       : 0.00
% 13.53/6.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
