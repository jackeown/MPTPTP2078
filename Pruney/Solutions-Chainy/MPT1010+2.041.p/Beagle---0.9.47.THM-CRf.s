%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:10 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 109 expanded)
%              Number of leaves         :   40 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  113 ( 203 expanded)
%              Number of equality atoms :   34 (  68 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_99,axiom,(
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

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_67,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_56,plain,(
    k1_funct_1('#skF_7','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_60,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_248,plain,(
    ! [C_75,B_76,A_77] :
      ( v5_relat_1(C_75,B_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_77,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_252,plain,(
    v5_relat_1('#skF_7',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_60,c_248])).

tff(c_58,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_165,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_169,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_165])).

tff(c_64,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_62,plain,(
    v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_253,plain,(
    ! [A_78,B_79,C_80] :
      ( k1_relset_1(A_78,B_79,C_80) = k1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_257,plain,(
    k1_relset_1('#skF_4',k1_tarski('#skF_5'),'#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_253])).

tff(c_372,plain,(
    ! [B_108,A_109,C_110] :
      ( k1_xboole_0 = B_108
      | k1_relset_1(A_109,B_108,C_110) = A_109
      | ~ v1_funct_2(C_110,A_109,B_108)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_109,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_375,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | k1_relset_1('#skF_4',k1_tarski('#skF_5'),'#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_60,c_372])).

tff(c_378,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_257,c_375])).

tff(c_379,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_378])).

tff(c_32,plain,(
    ! [C_19,B_18,A_17] :
      ( m1_subset_1(k1_funct_1(C_19,B_18),A_17)
      | ~ r2_hidden(B_18,k1_relat_1(C_19))
      | ~ v1_funct_1(C_19)
      | ~ v5_relat_1(C_19,A_17)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_383,plain,(
    ! [B_18,A_17] :
      ( m1_subset_1(k1_funct_1('#skF_7',B_18),A_17)
      | ~ r2_hidden(B_18,'#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_17)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_32])).

tff(c_393,plain,(
    ! [B_111,A_112] :
      ( m1_subset_1(k1_funct_1('#skF_7',B_111),A_112)
      | ~ r2_hidden(B_111,'#skF_4')
      | ~ v5_relat_1('#skF_7',A_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_64,c_383])).

tff(c_82,plain,(
    ! [A_43] : k2_tarski(A_43,A_43) = k1_tarski(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_71,plain,(
    ! [D_37,A_38] : r2_hidden(D_37,k2_tarski(A_38,D_37)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [A_38,D_37] : ~ v1_xboole_0(k2_tarski(A_38,D_37)) ),
    inference(resolution,[status(thm)],[c_71,c_2])).

tff(c_90,plain,(
    ! [A_43] : ~ v1_xboole_0(k1_tarski(A_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_75])).

tff(c_30,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,B_16)
      | v1_xboole_0(B_16)
      | ~ m1_subset_1(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_181,plain,(
    ! [D_67,B_68,A_69] :
      ( D_67 = B_68
      | D_67 = A_69
      | ~ r2_hidden(D_67,k2_tarski(A_69,B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_209,plain,(
    ! [D_70,A_71] :
      ( D_70 = A_71
      | D_70 = A_71
      | ~ r2_hidden(D_70,k1_tarski(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_181])).

tff(c_213,plain,(
    ! [A_71,A_15] :
      ( A_71 = A_15
      | v1_xboole_0(k1_tarski(A_71))
      | ~ m1_subset_1(A_15,k1_tarski(A_71)) ) ),
    inference(resolution,[status(thm)],[c_30,c_209])).

tff(c_223,plain,(
    ! [A_71,A_15] :
      ( A_71 = A_15
      | ~ m1_subset_1(A_15,k1_tarski(A_71)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_213])).

tff(c_449,plain,(
    ! [B_113,A_114] :
      ( k1_funct_1('#skF_7',B_113) = A_114
      | ~ r2_hidden(B_113,'#skF_4')
      | ~ v5_relat_1('#skF_7',k1_tarski(A_114)) ) ),
    inference(resolution,[status(thm)],[c_393,c_223])).

tff(c_1012,plain,(
    ! [A_1353] :
      ( k1_funct_1('#skF_7','#skF_6') = A_1353
      | ~ v5_relat_1('#skF_7',k1_tarski(A_1353)) ) ),
    inference(resolution,[status(thm)],[c_58,c_449])).

tff(c_1016,plain,(
    k1_funct_1('#skF_7','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_252,c_1012])).

tff(c_1020,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1016])).

tff(c_1021,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_378])).

tff(c_12,plain,(
    ! [D_11,B_7] : r2_hidden(D_11,k2_tarski(D_11,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_88,plain,(
    ! [A_43] : r2_hidden(A_43,k1_tarski(A_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_12])).

tff(c_111,plain,(
    ! [B_47,A_48] :
      ( ~ r1_tarski(B_47,A_48)
      | ~ r2_hidden(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_128,plain,(
    ! [A_43] : ~ r1_tarski(k1_tarski(A_43),A_43) ),
    inference(resolution,[status(thm)],[c_88,c_111])).

tff(c_1039,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1021,c_128])).

tff(c_1049,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1039])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:17:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.46  
% 3.10/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.46  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 3.10/1.46  
% 3.10/1.46  %Foreground sorts:
% 3.10/1.46  
% 3.10/1.46  
% 3.10/1.46  %Background operators:
% 3.10/1.46  
% 3.10/1.46  
% 3.10/1.46  %Foreground operators:
% 3.10/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.10/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.10/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.10/1.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.10/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.10/1.46  tff('#skF_7', type, '#skF_7': $i).
% 3.10/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.10/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.10/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.10/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.10/1.46  tff('#skF_6', type, '#skF_6': $i).
% 3.10/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.10/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.10/1.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.10/1.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.10/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.10/1.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.10/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.10/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.10/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.10/1.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.10/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.10/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.10/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.10/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.10/1.46  
% 3.10/1.47  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.10/1.47  tff(f_110, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 3.10/1.47  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.10/1.47  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.10/1.47  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.10/1.47  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.10/1.47  tff(f_62, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_1)).
% 3.10/1.47  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.10/1.47  tff(f_42, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.10/1.47  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.10/1.47  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.10/1.47  tff(f_67, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.10/1.47  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.10/1.47  tff(c_56, plain, (k1_funct_1('#skF_7', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.10/1.47  tff(c_60, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.10/1.47  tff(c_248, plain, (![C_75, B_76, A_77]: (v5_relat_1(C_75, B_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_77, B_76))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.10/1.47  tff(c_252, plain, (v5_relat_1('#skF_7', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_248])).
% 3.10/1.47  tff(c_58, plain, (r2_hidden('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.10/1.47  tff(c_165, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.10/1.47  tff(c_169, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_60, c_165])).
% 3.10/1.47  tff(c_64, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.10/1.47  tff(c_62, plain, (v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.10/1.47  tff(c_253, plain, (![A_78, B_79, C_80]: (k1_relset_1(A_78, B_79, C_80)=k1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.10/1.47  tff(c_257, plain, (k1_relset_1('#skF_4', k1_tarski('#skF_5'), '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_60, c_253])).
% 3.10/1.47  tff(c_372, plain, (![B_108, A_109, C_110]: (k1_xboole_0=B_108 | k1_relset_1(A_109, B_108, C_110)=A_109 | ~v1_funct_2(C_110, A_109, B_108) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_109, B_108))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.10/1.47  tff(c_375, plain, (k1_tarski('#skF_5')=k1_xboole_0 | k1_relset_1('#skF_4', k1_tarski('#skF_5'), '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_60, c_372])).
% 3.10/1.47  tff(c_378, plain, (k1_tarski('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_257, c_375])).
% 3.10/1.47  tff(c_379, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_378])).
% 3.10/1.47  tff(c_32, plain, (![C_19, B_18, A_17]: (m1_subset_1(k1_funct_1(C_19, B_18), A_17) | ~r2_hidden(B_18, k1_relat_1(C_19)) | ~v1_funct_1(C_19) | ~v5_relat_1(C_19, A_17) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.10/1.47  tff(c_383, plain, (![B_18, A_17]: (m1_subset_1(k1_funct_1('#skF_7', B_18), A_17) | ~r2_hidden(B_18, '#skF_4') | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_17) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_379, c_32])).
% 3.10/1.47  tff(c_393, plain, (![B_111, A_112]: (m1_subset_1(k1_funct_1('#skF_7', B_111), A_112) | ~r2_hidden(B_111, '#skF_4') | ~v5_relat_1('#skF_7', A_112))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_64, c_383])).
% 3.10/1.47  tff(c_82, plain, (![A_43]: (k2_tarski(A_43, A_43)=k1_tarski(A_43))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.10/1.47  tff(c_71, plain, (![D_37, A_38]: (r2_hidden(D_37, k2_tarski(A_38, D_37)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.10/1.47  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.10/1.47  tff(c_75, plain, (![A_38, D_37]: (~v1_xboole_0(k2_tarski(A_38, D_37)))), inference(resolution, [status(thm)], [c_71, c_2])).
% 3.10/1.47  tff(c_90, plain, (![A_43]: (~v1_xboole_0(k1_tarski(A_43)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_75])).
% 3.10/1.47  tff(c_30, plain, (![A_15, B_16]: (r2_hidden(A_15, B_16) | v1_xboole_0(B_16) | ~m1_subset_1(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.10/1.47  tff(c_26, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.10/1.47  tff(c_181, plain, (![D_67, B_68, A_69]: (D_67=B_68 | D_67=A_69 | ~r2_hidden(D_67, k2_tarski(A_69, B_68)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.10/1.47  tff(c_209, plain, (![D_70, A_71]: (D_70=A_71 | D_70=A_71 | ~r2_hidden(D_70, k1_tarski(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_181])).
% 3.10/1.47  tff(c_213, plain, (![A_71, A_15]: (A_71=A_15 | v1_xboole_0(k1_tarski(A_71)) | ~m1_subset_1(A_15, k1_tarski(A_71)))), inference(resolution, [status(thm)], [c_30, c_209])).
% 3.10/1.47  tff(c_223, plain, (![A_71, A_15]: (A_71=A_15 | ~m1_subset_1(A_15, k1_tarski(A_71)))), inference(negUnitSimplification, [status(thm)], [c_90, c_213])).
% 3.10/1.47  tff(c_449, plain, (![B_113, A_114]: (k1_funct_1('#skF_7', B_113)=A_114 | ~r2_hidden(B_113, '#skF_4') | ~v5_relat_1('#skF_7', k1_tarski(A_114)))), inference(resolution, [status(thm)], [c_393, c_223])).
% 3.10/1.47  tff(c_1012, plain, (![A_1353]: (k1_funct_1('#skF_7', '#skF_6')=A_1353 | ~v5_relat_1('#skF_7', k1_tarski(A_1353)))), inference(resolution, [status(thm)], [c_58, c_449])).
% 3.10/1.47  tff(c_1016, plain, (k1_funct_1('#skF_7', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_252, c_1012])).
% 3.10/1.47  tff(c_1020, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1016])).
% 3.10/1.47  tff(c_1021, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_378])).
% 3.10/1.47  tff(c_12, plain, (![D_11, B_7]: (r2_hidden(D_11, k2_tarski(D_11, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.10/1.47  tff(c_88, plain, (![A_43]: (r2_hidden(A_43, k1_tarski(A_43)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_12])).
% 3.10/1.47  tff(c_111, plain, (![B_47, A_48]: (~r1_tarski(B_47, A_48) | ~r2_hidden(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.10/1.47  tff(c_128, plain, (![A_43]: (~r1_tarski(k1_tarski(A_43), A_43))), inference(resolution, [status(thm)], [c_88, c_111])).
% 3.10/1.47  tff(c_1039, plain, (~r1_tarski(k1_xboole_0, '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1021, c_128])).
% 3.10/1.47  tff(c_1049, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1039])).
% 3.10/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.47  
% 3.10/1.47  Inference rules
% 3.10/1.47  ----------------------
% 3.10/1.47  #Ref     : 0
% 3.10/1.47  #Sup     : 146
% 3.10/1.47  #Fact    : 4
% 3.10/1.47  #Define  : 0
% 3.10/1.47  #Split   : 1
% 3.10/1.47  #Chain   : 0
% 3.10/1.47  #Close   : 0
% 3.10/1.47  
% 3.10/1.47  Ordering : KBO
% 3.10/1.47  
% 3.10/1.47  Simplification rules
% 3.10/1.47  ----------------------
% 3.10/1.47  #Subsume      : 16
% 3.10/1.47  #Demod        : 29
% 3.10/1.48  #Tautology    : 36
% 3.10/1.48  #SimpNegUnit  : 13
% 3.10/1.48  #BackRed      : 5
% 3.10/1.48  
% 3.10/1.48  #Partial instantiations: 880
% 3.10/1.48  #Strategies tried      : 1
% 3.10/1.48  
% 3.10/1.48  Timing (in seconds)
% 3.10/1.48  ----------------------
% 3.10/1.48  Preprocessing        : 0.33
% 3.10/1.48  Parsing              : 0.17
% 3.10/1.48  CNF conversion       : 0.02
% 3.10/1.48  Main loop            : 0.38
% 3.10/1.48  Inferencing          : 0.18
% 3.10/1.48  Reduction            : 0.10
% 3.10/1.48  Demodulation         : 0.07
% 3.10/1.48  BG Simplification    : 0.02
% 3.10/1.48  Subsumption          : 0.05
% 3.10/1.48  Abstraction          : 0.02
% 3.10/1.48  MUC search           : 0.00
% 3.10/1.48  Cooper               : 0.00
% 3.10/1.48  Total                : 0.75
% 3.10/1.48  Index Insertion      : 0.00
% 3.10/1.48  Index Deletion       : 0.00
% 3.10/1.48  Index Matching       : 0.00
% 3.10/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
