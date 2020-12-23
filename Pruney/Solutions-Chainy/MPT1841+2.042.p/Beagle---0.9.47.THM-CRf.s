%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:33 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 483 expanded)
%              Number of leaves         :   37 ( 179 expanded)
%              Depth                    :   16
%              Number of atoms          :  158 (1189 expanded)
%              Number of equality atoms :   56 ( 295 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_4 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_107,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_62,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_80,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_74,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_subset_1(B,A)
           => ~ v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_subset_1)).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    v1_zfmisc_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_46,plain,(
    ! [A_31] :
      ( k6_domain_1(A_31,'#skF_5'(A_31)) = A_31
      | ~ v1_zfmisc_1(A_31)
      | v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_48,plain,(
    ! [A_31] :
      ( m1_subset_1('#skF_5'(A_31),A_31)
      | ~ v1_zfmisc_1(A_31)
      | v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_219,plain,(
    ! [A_67,B_68] :
      ( k6_domain_1(A_67,B_68) = k1_tarski(B_68)
      | ~ m1_subset_1(B_68,A_67)
      | v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_323,plain,(
    ! [A_81] :
      ( k6_domain_1(A_81,'#skF_5'(A_81)) = k1_tarski('#skF_5'(A_81))
      | ~ v1_zfmisc_1(A_81)
      | v1_xboole_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_48,c_219])).

tff(c_593,plain,(
    ! [A_106] :
      ( k1_tarski('#skF_5'(A_106)) = A_106
      | ~ v1_zfmisc_1(A_106)
      | v1_xboole_0(A_106)
      | ~ v1_zfmisc_1(A_106)
      | v1_xboole_0(A_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_323])).

tff(c_16,plain,(
    ! [C_14] : r2_hidden(C_14,k1_tarski(C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_68,plain,(
    ! [B_39,A_40] :
      ( ~ r2_hidden(B_39,A_40)
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [C_14] : ~ v1_xboole_0(k1_tarski(C_14)) ),
    inference(resolution,[status(thm)],[c_16,c_68])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    ! [C_47,A_48] :
      ( C_47 = A_48
      | ~ r2_hidden(C_47,k1_tarski(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_90,plain,(
    ! [A_48] :
      ( '#skF_1'(k1_tarski(A_48)) = A_48
      | v1_xboole_0(k1_tarski(A_48)) ) ),
    inference(resolution,[status(thm)],[c_4,c_86])).

tff(c_96,plain,(
    ! [A_48] : '#skF_1'(k1_tarski(A_48)) = A_48 ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_90])).

tff(c_710,plain,(
    ! [A_113] :
      ( '#skF_5'(A_113) = '#skF_1'(A_113)
      | ~ v1_zfmisc_1(A_113)
      | v1_xboole_0(A_113)
      | ~ v1_zfmisc_1(A_113)
      | v1_xboole_0(A_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_593,c_96])).

tff(c_714,plain,
    ( '#skF_5'('#skF_6') = '#skF_1'('#skF_6')
    | ~ v1_zfmisc_1('#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_710])).

tff(c_718,plain,
    ( '#skF_5'('#skF_6') = '#skF_1'('#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_714])).

tff(c_719,plain,(
    '#skF_5'('#skF_6') = '#skF_1'('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_718])).

tff(c_335,plain,(
    ! [A_31] :
      ( k1_tarski('#skF_5'(A_31)) = A_31
      | ~ v1_zfmisc_1(A_31)
      | v1_xboole_0(A_31)
      | ~ v1_zfmisc_1(A_31)
      | v1_xboole_0(A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_323])).

tff(c_726,plain,
    ( k1_tarski('#skF_1'('#skF_6')) = '#skF_6'
    | ~ v1_zfmisc_1('#skF_6')
    | v1_xboole_0('#skF_6')
    | ~ v1_zfmisc_1('#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_719,c_335])).

tff(c_742,plain,
    ( k1_tarski('#skF_1'('#skF_6')) = '#skF_6'
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_726])).

tff(c_743,plain,(
    k1_tarski('#skF_1'('#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_742])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_75,plain,(
    ! [A_43,B_44] : k2_xboole_0(k1_tarski(A_43),B_44) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_79,plain,(
    ! [A_43] : k1_tarski(A_43) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_75])).

tff(c_34,plain,(
    ! [A_23] : m1_subset_1('#skF_4'(A_23),k1_zfmisc_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_115,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_133,plain,(
    ! [A_58] : r1_tarski('#skF_4'(A_58),A_58) ),
    inference(resolution,[status(thm)],[c_34,c_115])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_137,plain,(
    ! [A_58] : k2_xboole_0('#skF_4'(A_58),A_58) = A_58 ),
    inference(resolution,[status(thm)],[c_133,c_8])).

tff(c_294,plain,(
    ! [C_73,B_74,A_75] :
      ( k1_xboole_0 = C_73
      | k1_xboole_0 = B_74
      | C_73 = B_74
      | k2_xboole_0(B_74,C_73) != k1_tarski(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_297,plain,(
    ! [A_58,A_75] :
      ( k1_xboole_0 = A_58
      | '#skF_4'(A_58) = k1_xboole_0
      | '#skF_4'(A_58) = A_58
      | k1_tarski(A_75) != A_58 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_294])).

tff(c_430,plain,(
    ! [A_75] :
      ( k1_tarski(A_75) = k1_xboole_0
      | '#skF_4'(k1_tarski(A_75)) = k1_xboole_0
      | '#skF_4'(k1_tarski(A_75)) = k1_tarski(A_75) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_297])).

tff(c_437,plain,(
    ! [A_95] :
      ( '#skF_4'(k1_tarski(A_95)) = k1_xboole_0
      | '#skF_4'(k1_tarski(A_95)) = k1_tarski(A_95) ) ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_430])).

tff(c_32,plain,(
    ! [A_23] : ~ v1_subset_1('#skF_4'(A_23),A_23) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_458,plain,(
    ! [A_95] :
      ( ~ v1_subset_1(k1_tarski(A_95),k1_tarski(A_95))
      | '#skF_4'(k1_tarski(A_95)) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_32])).

tff(c_773,plain,
    ( ~ v1_subset_1('#skF_6',k1_tarski('#skF_1'('#skF_6')))
    | '#skF_4'(k1_tarski('#skF_1'('#skF_6'))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_743,c_458])).

tff(c_816,plain,
    ( ~ v1_subset_1('#skF_6','#skF_6')
    | '#skF_4'('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_743,c_743,c_773])).

tff(c_878,plain,(
    ~ v1_subset_1('#skF_6','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_816])).

tff(c_54,plain,(
    m1_subset_1('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_178,plain,(
    ! [A_60,B_61] :
      ( r2_hidden(A_60,B_61)
      | v1_xboole_0(B_61)
      | ~ m1_subset_1(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_14,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_182,plain,(
    ! [A_60,A_10] :
      ( A_60 = A_10
      | v1_xboole_0(k1_tarski(A_10))
      | ~ m1_subset_1(A_60,k1_tarski(A_10)) ) ),
    inference(resolution,[status(thm)],[c_178,c_14])).

tff(c_188,plain,(
    ! [A_60,A_10] :
      ( A_60 = A_10
      | ~ m1_subset_1(A_60,k1_tarski(A_10)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_182])).

tff(c_1043,plain,(
    ! [A_120] :
      ( A_120 = '#skF_1'('#skF_6')
      | ~ m1_subset_1(A_120,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_743,c_188])).

tff(c_1060,plain,(
    '#skF_1'('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_54,c_1043])).

tff(c_1079,plain,(
    k1_tarski('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1060,c_743])).

tff(c_234,plain,
    ( k6_domain_1('#skF_6','#skF_7') = k1_tarski('#skF_7')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_219])).

tff(c_241,plain,(
    k6_domain_1('#skF_6','#skF_7') = k1_tarski('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_234])).

tff(c_52,plain,(
    v1_subset_1(k6_domain_1('#skF_6','#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_242,plain,(
    v1_subset_1(k1_tarski('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_52])).

tff(c_1091,plain,(
    v1_subset_1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1079,c_242])).

tff(c_1094,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_878,c_1091])).

tff(c_1095,plain,(
    '#skF_4'('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_816])).

tff(c_271,plain,(
    ! [B_71,A_72] :
      ( ~ v1_xboole_0(B_71)
      | v1_subset_1(B_71,A_72)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72))
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_284,plain,(
    ! [A_23] :
      ( ~ v1_xboole_0('#skF_4'(A_23))
      | v1_subset_1('#skF_4'(A_23),A_23)
      | v1_xboole_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_34,c_271])).

tff(c_293,plain,(
    ! [A_23] :
      ( ~ v1_xboole_0('#skF_4'(A_23))
      | v1_xboole_0(A_23) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_284])).

tff(c_1106,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1095,c_293])).

tff(c_1123,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1106])).

tff(c_1125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1123])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:39:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.52  
% 3.53/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.53  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_4 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2
% 3.53/1.53  
% 3.53/1.53  %Foreground sorts:
% 3.53/1.53  
% 3.53/1.53  
% 3.53/1.53  %Background operators:
% 3.53/1.53  
% 3.53/1.53  
% 3.53/1.53  %Foreground operators:
% 3.53/1.53  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.53/1.53  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.53/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.53/1.53  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.53/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.53/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.53/1.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.53/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.53/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.53/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.53/1.53  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.53/1.53  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.53/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.53/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.53/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.53/1.53  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.53/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.53/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.53/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.53/1.53  
% 3.61/1.55  tff(f_119, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 3.61/1.55  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.61/1.55  tff(f_107, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 3.61/1.55  tff(f_97, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.61/1.55  tff(f_47, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.61/1.55  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.61/1.55  tff(f_38, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.61/1.55  tff(f_62, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.61/1.55  tff(f_80, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_subset_1)).
% 3.61/1.55  tff(f_90, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.61/1.55  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.61/1.55  tff(f_59, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 3.61/1.55  tff(f_86, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.61/1.55  tff(f_74, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_subset_1(B, A) => ~v1_xboole_0(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_subset_1)).
% 3.61/1.55  tff(c_56, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.61/1.55  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.61/1.55  tff(c_50, plain, (v1_zfmisc_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.61/1.55  tff(c_46, plain, (![A_31]: (k6_domain_1(A_31, '#skF_5'(A_31))=A_31 | ~v1_zfmisc_1(A_31) | v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.61/1.55  tff(c_48, plain, (![A_31]: (m1_subset_1('#skF_5'(A_31), A_31) | ~v1_zfmisc_1(A_31) | v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.61/1.55  tff(c_219, plain, (![A_67, B_68]: (k6_domain_1(A_67, B_68)=k1_tarski(B_68) | ~m1_subset_1(B_68, A_67) | v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.61/1.55  tff(c_323, plain, (![A_81]: (k6_domain_1(A_81, '#skF_5'(A_81))=k1_tarski('#skF_5'(A_81)) | ~v1_zfmisc_1(A_81) | v1_xboole_0(A_81))), inference(resolution, [status(thm)], [c_48, c_219])).
% 3.61/1.55  tff(c_593, plain, (![A_106]: (k1_tarski('#skF_5'(A_106))=A_106 | ~v1_zfmisc_1(A_106) | v1_xboole_0(A_106) | ~v1_zfmisc_1(A_106) | v1_xboole_0(A_106))), inference(superposition, [status(thm), theory('equality')], [c_46, c_323])).
% 3.61/1.55  tff(c_16, plain, (![C_14]: (r2_hidden(C_14, k1_tarski(C_14)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.61/1.55  tff(c_68, plain, (![B_39, A_40]: (~r2_hidden(B_39, A_40) | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.61/1.55  tff(c_72, plain, (![C_14]: (~v1_xboole_0(k1_tarski(C_14)))), inference(resolution, [status(thm)], [c_16, c_68])).
% 3.61/1.55  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.61/1.55  tff(c_86, plain, (![C_47, A_48]: (C_47=A_48 | ~r2_hidden(C_47, k1_tarski(A_48)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.61/1.55  tff(c_90, plain, (![A_48]: ('#skF_1'(k1_tarski(A_48))=A_48 | v1_xboole_0(k1_tarski(A_48)))), inference(resolution, [status(thm)], [c_4, c_86])).
% 3.61/1.55  tff(c_96, plain, (![A_48]: ('#skF_1'(k1_tarski(A_48))=A_48)), inference(negUnitSimplification, [status(thm)], [c_72, c_90])).
% 3.61/1.55  tff(c_710, plain, (![A_113]: ('#skF_5'(A_113)='#skF_1'(A_113) | ~v1_zfmisc_1(A_113) | v1_xboole_0(A_113) | ~v1_zfmisc_1(A_113) | v1_xboole_0(A_113))), inference(superposition, [status(thm), theory('equality')], [c_593, c_96])).
% 3.61/1.55  tff(c_714, plain, ('#skF_5'('#skF_6')='#skF_1'('#skF_6') | ~v1_zfmisc_1('#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_50, c_710])).
% 3.61/1.55  tff(c_718, plain, ('#skF_5'('#skF_6')='#skF_1'('#skF_6') | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_714])).
% 3.61/1.55  tff(c_719, plain, ('#skF_5'('#skF_6')='#skF_1'('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_56, c_718])).
% 3.61/1.55  tff(c_335, plain, (![A_31]: (k1_tarski('#skF_5'(A_31))=A_31 | ~v1_zfmisc_1(A_31) | v1_xboole_0(A_31) | ~v1_zfmisc_1(A_31) | v1_xboole_0(A_31))), inference(superposition, [status(thm), theory('equality')], [c_46, c_323])).
% 3.61/1.55  tff(c_726, plain, (k1_tarski('#skF_1'('#skF_6'))='#skF_6' | ~v1_zfmisc_1('#skF_6') | v1_xboole_0('#skF_6') | ~v1_zfmisc_1('#skF_6') | v1_xboole_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_719, c_335])).
% 3.61/1.55  tff(c_742, plain, (k1_tarski('#skF_1'('#skF_6'))='#skF_6' | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_726])).
% 3.61/1.55  tff(c_743, plain, (k1_tarski('#skF_1'('#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_56, c_742])).
% 3.61/1.55  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.61/1.55  tff(c_75, plain, (![A_43, B_44]: (k2_xboole_0(k1_tarski(A_43), B_44)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.61/1.55  tff(c_79, plain, (![A_43]: (k1_tarski(A_43)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_75])).
% 3.61/1.55  tff(c_34, plain, (![A_23]: (m1_subset_1('#skF_4'(A_23), k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.61/1.55  tff(c_115, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~m1_subset_1(A_54, k1_zfmisc_1(B_55)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.61/1.55  tff(c_133, plain, (![A_58]: (r1_tarski('#skF_4'(A_58), A_58))), inference(resolution, [status(thm)], [c_34, c_115])).
% 3.61/1.55  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.61/1.55  tff(c_137, plain, (![A_58]: (k2_xboole_0('#skF_4'(A_58), A_58)=A_58)), inference(resolution, [status(thm)], [c_133, c_8])).
% 3.61/1.55  tff(c_294, plain, (![C_73, B_74, A_75]: (k1_xboole_0=C_73 | k1_xboole_0=B_74 | C_73=B_74 | k2_xboole_0(B_74, C_73)!=k1_tarski(A_75))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.61/1.55  tff(c_297, plain, (![A_58, A_75]: (k1_xboole_0=A_58 | '#skF_4'(A_58)=k1_xboole_0 | '#skF_4'(A_58)=A_58 | k1_tarski(A_75)!=A_58)), inference(superposition, [status(thm), theory('equality')], [c_137, c_294])).
% 3.61/1.55  tff(c_430, plain, (![A_75]: (k1_tarski(A_75)=k1_xboole_0 | '#skF_4'(k1_tarski(A_75))=k1_xboole_0 | '#skF_4'(k1_tarski(A_75))=k1_tarski(A_75))), inference(reflexivity, [status(thm), theory('equality')], [c_297])).
% 3.61/1.55  tff(c_437, plain, (![A_95]: ('#skF_4'(k1_tarski(A_95))=k1_xboole_0 | '#skF_4'(k1_tarski(A_95))=k1_tarski(A_95))), inference(negUnitSimplification, [status(thm)], [c_79, c_430])).
% 3.61/1.55  tff(c_32, plain, (![A_23]: (~v1_subset_1('#skF_4'(A_23), A_23))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.61/1.55  tff(c_458, plain, (![A_95]: (~v1_subset_1(k1_tarski(A_95), k1_tarski(A_95)) | '#skF_4'(k1_tarski(A_95))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_437, c_32])).
% 3.61/1.55  tff(c_773, plain, (~v1_subset_1('#skF_6', k1_tarski('#skF_1'('#skF_6'))) | '#skF_4'(k1_tarski('#skF_1'('#skF_6')))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_743, c_458])).
% 3.61/1.55  tff(c_816, plain, (~v1_subset_1('#skF_6', '#skF_6') | '#skF_4'('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_743, c_743, c_773])).
% 3.61/1.55  tff(c_878, plain, (~v1_subset_1('#skF_6', '#skF_6')), inference(splitLeft, [status(thm)], [c_816])).
% 3.61/1.55  tff(c_54, plain, (m1_subset_1('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.61/1.55  tff(c_178, plain, (![A_60, B_61]: (r2_hidden(A_60, B_61) | v1_xboole_0(B_61) | ~m1_subset_1(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.61/1.55  tff(c_14, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.61/1.55  tff(c_182, plain, (![A_60, A_10]: (A_60=A_10 | v1_xboole_0(k1_tarski(A_10)) | ~m1_subset_1(A_60, k1_tarski(A_10)))), inference(resolution, [status(thm)], [c_178, c_14])).
% 3.61/1.55  tff(c_188, plain, (![A_60, A_10]: (A_60=A_10 | ~m1_subset_1(A_60, k1_tarski(A_10)))), inference(negUnitSimplification, [status(thm)], [c_72, c_182])).
% 3.61/1.55  tff(c_1043, plain, (![A_120]: (A_120='#skF_1'('#skF_6') | ~m1_subset_1(A_120, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_743, c_188])).
% 3.61/1.55  tff(c_1060, plain, ('#skF_1'('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_54, c_1043])).
% 3.61/1.55  tff(c_1079, plain, (k1_tarski('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1060, c_743])).
% 3.61/1.55  tff(c_234, plain, (k6_domain_1('#skF_6', '#skF_7')=k1_tarski('#skF_7') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_54, c_219])).
% 3.61/1.55  tff(c_241, plain, (k6_domain_1('#skF_6', '#skF_7')=k1_tarski('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_56, c_234])).
% 3.61/1.55  tff(c_52, plain, (v1_subset_1(k6_domain_1('#skF_6', '#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.61/1.55  tff(c_242, plain, (v1_subset_1(k1_tarski('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_241, c_52])).
% 3.61/1.55  tff(c_1091, plain, (v1_subset_1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1079, c_242])).
% 3.61/1.55  tff(c_1094, plain, $false, inference(negUnitSimplification, [status(thm)], [c_878, c_1091])).
% 3.61/1.55  tff(c_1095, plain, ('#skF_4'('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_816])).
% 3.61/1.55  tff(c_271, plain, (![B_71, A_72]: (~v1_xboole_0(B_71) | v1_subset_1(B_71, A_72) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.61/1.55  tff(c_284, plain, (![A_23]: (~v1_xboole_0('#skF_4'(A_23)) | v1_subset_1('#skF_4'(A_23), A_23) | v1_xboole_0(A_23))), inference(resolution, [status(thm)], [c_34, c_271])).
% 3.61/1.55  tff(c_293, plain, (![A_23]: (~v1_xboole_0('#skF_4'(A_23)) | v1_xboole_0(A_23))), inference(negUnitSimplification, [status(thm)], [c_32, c_284])).
% 3.61/1.55  tff(c_1106, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1095, c_293])).
% 3.61/1.55  tff(c_1123, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1106])).
% 3.61/1.55  tff(c_1125, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1123])).
% 3.61/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.55  
% 3.61/1.55  Inference rules
% 3.61/1.55  ----------------------
% 3.61/1.55  #Ref     : 1
% 3.61/1.55  #Sup     : 245
% 3.61/1.55  #Fact    : 1
% 3.61/1.55  #Define  : 0
% 3.61/1.55  #Split   : 3
% 3.61/1.55  #Chain   : 0
% 3.61/1.55  #Close   : 0
% 3.61/1.55  
% 3.61/1.55  Ordering : KBO
% 3.61/1.55  
% 3.61/1.55  Simplification rules
% 3.61/1.55  ----------------------
% 3.61/1.55  #Subsume      : 26
% 3.61/1.55  #Demod        : 102
% 3.61/1.55  #Tautology    : 102
% 3.61/1.55  #SimpNegUnit  : 45
% 3.61/1.55  #BackRed      : 11
% 3.61/1.55  
% 3.61/1.55  #Partial instantiations: 0
% 3.61/1.55  #Strategies tried      : 1
% 3.61/1.55  
% 3.61/1.55  Timing (in seconds)
% 3.61/1.55  ----------------------
% 3.61/1.55  Preprocessing        : 0.34
% 3.61/1.55  Parsing              : 0.18
% 3.61/1.55  CNF conversion       : 0.03
% 3.61/1.55  Main loop            : 0.44
% 3.61/1.55  Inferencing          : 0.16
% 3.61/1.55  Reduction            : 0.14
% 3.61/1.55  Demodulation         : 0.08
% 3.61/1.55  BG Simplification    : 0.03
% 3.61/1.55  Subsumption          : 0.08
% 3.61/1.55  Abstraction          : 0.02
% 3.61/1.55  MUC search           : 0.00
% 3.61/1.55  Cooper               : 0.00
% 3.61/1.55  Total                : 0.83
% 3.61/1.55  Index Insertion      : 0.00
% 3.61/1.55  Index Deletion       : 0.00
% 3.61/1.55  Index Matching       : 0.00
% 3.61/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
