%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:54 EST 2020

% Result     : Theorem 4.63s
% Output     : CNFRefutation 4.68s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 318 expanded)
%              Number of leaves         :   46 ( 131 expanded)
%              Depth                    :   12
%              Number of atoms          :  222 (1067 expanded)
%              Number of equality atoms :   50 ( 253 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k7_partfun1(A,E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_139,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ! [E] :
              ( ( v1_funct_1(E)
                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                   => ( B = k1_xboole_0
                      | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_104,axiom,(
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

tff(f_115,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_56,plain,(
    m1_subset_1('#skF_8','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_60,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_58,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_375,plain,(
    ! [A_128,B_129,C_130] :
      ( k1_relset_1(A_128,B_129,C_130) = k1_relat_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_382,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_375])).

tff(c_62,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_299,plain,(
    ! [A_117,B_118,C_119] :
      ( k2_relset_1(A_117,B_118,C_119) = k2_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_307,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_299])).

tff(c_54,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_312,plain,(
    r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_54])).

tff(c_385,plain,(
    r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_312])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_66,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_64,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_1351,plain,(
    ! [A_235,D_238,B_236,F_240,E_237,C_239] :
      ( k1_funct_1(k8_funct_2(B_236,C_239,A_235,D_238,E_237),F_240) = k1_funct_1(E_237,k1_funct_1(D_238,F_240))
      | k1_xboole_0 = B_236
      | ~ r1_tarski(k2_relset_1(B_236,C_239,D_238),k1_relset_1(C_239,A_235,E_237))
      | ~ m1_subset_1(F_240,B_236)
      | ~ m1_subset_1(E_237,k1_zfmisc_1(k2_zfmisc_1(C_239,A_235)))
      | ~ v1_funct_1(E_237)
      | ~ m1_subset_1(D_238,k1_zfmisc_1(k2_zfmisc_1(B_236,C_239)))
      | ~ v1_funct_2(D_238,B_236,C_239)
      | ~ v1_funct_1(D_238)
      | v1_xboole_0(C_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1357,plain,(
    ! [A_235,E_237,F_240] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5',A_235,'#skF_6',E_237),F_240) = k1_funct_1(E_237,k1_funct_1('#skF_6',F_240))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5',A_235,E_237))
      | ~ m1_subset_1(F_240,'#skF_4')
      | ~ m1_subset_1(E_237,k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_235)))
      | ~ v1_funct_1(E_237)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_1351])).

tff(c_1369,plain,(
    ! [A_235,E_237,F_240] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5',A_235,'#skF_6',E_237),F_240) = k1_funct_1(E_237,k1_funct_1('#skF_6',F_240))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5',A_235,E_237))
      | ~ m1_subset_1(F_240,'#skF_4')
      | ~ m1_subset_1(E_237,k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_235)))
      | ~ v1_funct_1(E_237)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_1357])).

tff(c_1388,plain,(
    ! [A_244,E_245,F_246] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5',A_244,'#skF_6',E_245),F_246) = k1_funct_1(E_245,k1_funct_1('#skF_6',F_246))
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5',A_244,E_245))
      | ~ m1_subset_1(F_246,'#skF_4')
      | ~ m1_subset_1(E_245,k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_244)))
      | ~ v1_funct_1(E_245) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_52,c_1369])).

tff(c_1390,plain,(
    ! [F_246] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_246) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_246))
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_246,'#skF_4')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
      | ~ v1_funct_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_1388])).

tff(c_1395,plain,(
    ! [F_246] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_246) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_246))
      | ~ m1_subset_1(F_246,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_385,c_1390])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_130,plain,(
    ! [B_86,A_87] :
      ( v1_relat_1(B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_87))
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_136,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_62,c_130])).

tff(c_142,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_136])).

tff(c_383,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_375])).

tff(c_1216,plain,(
    ! [B_224,A_225,C_226] :
      ( k1_xboole_0 = B_224
      | k1_relset_1(A_225,B_224,C_226) = A_225
      | ~ v1_funct_2(C_226,A_225,B_224)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(A_225,B_224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1222,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_1216])).

tff(c_1228,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_383,c_1222])).

tff(c_1229,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1228])).

tff(c_46,plain,(
    ! [A_35,B_36,C_38] :
      ( k7_partfun1(A_35,B_36,C_38) = k1_funct_1(B_36,C_38)
      | ~ r2_hidden(C_38,k1_relat_1(B_36))
      | ~ v1_funct_1(B_36)
      | ~ v5_relat_1(B_36,A_35)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1277,plain,(
    ! [A_35,C_38] :
      ( k7_partfun1(A_35,'#skF_6',C_38) = k1_funct_1('#skF_6',C_38)
      | ~ r2_hidden(C_38,'#skF_4')
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_35)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1229,c_46])).

tff(c_1307,plain,(
    ! [A_230,C_231] :
      ( k7_partfun1(A_230,'#skF_6',C_231) = k1_funct_1('#skF_6',C_231)
      | ~ r2_hidden(C_231,'#skF_4')
      | ~ v5_relat_1('#skF_6',A_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_66,c_1277])).

tff(c_1335,plain,(
    ! [A_230] :
      ( k7_partfun1(A_230,'#skF_6','#skF_1'('#skF_4')) = k1_funct_1('#skF_6','#skF_1'('#skF_4'))
      | ~ v5_relat_1('#skF_6',A_230)
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4,c_1307])).

tff(c_1341,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1335])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1344,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1341,c_12])).

tff(c_1348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1344])).

tff(c_1350,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1335])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_143,plain,(
    ! [C_88,B_89,A_90] :
      ( v5_relat_1(C_88,B_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_90,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_150,plain,(
    v5_relat_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_143])).

tff(c_133,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_58,c_130])).

tff(c_139,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_133])).

tff(c_836,plain,(
    ! [B_181,A_182] :
      ( r2_hidden(k1_funct_1(B_181,A_182),k2_relat_1(B_181))
      | ~ r2_hidden(A_182,k1_relat_1(B_181))
      | ~ v1_funct_1(B_181)
      | ~ v1_relat_1(B_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1421,plain,(
    ! [B_249,A_250,B_251] :
      ( r2_hidden(k1_funct_1(B_249,A_250),B_251)
      | ~ r1_tarski(k2_relat_1(B_249),B_251)
      | ~ r2_hidden(A_250,k1_relat_1(B_249))
      | ~ v1_funct_1(B_249)
      | ~ v1_relat_1(B_249) ) ),
    inference(resolution,[status(thm)],[c_836,c_6])).

tff(c_2220,plain,(
    ! [A_346,B_347,B_348,A_349] :
      ( k7_partfun1(A_346,B_347,k1_funct_1(B_348,A_349)) = k1_funct_1(B_347,k1_funct_1(B_348,A_349))
      | ~ v1_funct_1(B_347)
      | ~ v5_relat_1(B_347,A_346)
      | ~ v1_relat_1(B_347)
      | ~ r1_tarski(k2_relat_1(B_348),k1_relat_1(B_347))
      | ~ r2_hidden(A_349,k1_relat_1(B_348))
      | ~ v1_funct_1(B_348)
      | ~ v1_relat_1(B_348) ) ),
    inference(resolution,[status(thm)],[c_1421,c_46])).

tff(c_2224,plain,(
    ! [A_346,A_349] :
      ( k7_partfun1(A_346,'#skF_7',k1_funct_1('#skF_6',A_349)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_349))
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_346)
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(A_349,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_385,c_2220])).

tff(c_2234,plain,(
    ! [A_350,A_351] :
      ( k7_partfun1(A_350,'#skF_7',k1_funct_1('#skF_6',A_351)) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',A_351))
      | ~ v5_relat_1('#skF_7',A_350)
      | ~ r2_hidden(A_351,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_66,c_1229,c_139,c_60,c_2224])).

tff(c_50,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) != k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_2240,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ v5_relat_1('#skF_7','#skF_3')
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2234,c_50])).

tff(c_2246,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | ~ r2_hidden('#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_2240])).

tff(c_2248,plain,(
    ~ r2_hidden('#skF_8','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2246])).

tff(c_2251,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_2248])).

tff(c_2254,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2251])).

tff(c_2256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1350,c_2254])).

tff(c_2257,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_2246])).

tff(c_2381,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1395,c_2257])).

tff(c_2385,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2381])).

tff(c_2386,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1228])).

tff(c_14,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_78,plain,(
    ! [B_74,A_75] :
      ( ~ r1_tarski(B_74,A_75)
      | ~ r2_hidden(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_83,plain,(
    ! [A_76] :
      ( ~ r1_tarski(A_76,'#skF_1'(A_76))
      | v1_xboole_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_4,c_78])).

tff(c_88,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_83])).

tff(c_2397,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2386,c_88])).

tff(c_2402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2397])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n008.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 15:54:30 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.63/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.75  
% 4.68/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.75  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 4.68/1.75  
% 4.68/1.75  %Foreground sorts:
% 4.68/1.75  
% 4.68/1.75  
% 4.68/1.75  %Background operators:
% 4.68/1.75  
% 4.68/1.75  
% 4.68/1.75  %Foreground operators:
% 4.68/1.75  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.68/1.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.68/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.68/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.68/1.75  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.68/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.68/1.75  tff('#skF_7', type, '#skF_7': $i).
% 4.68/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.68/1.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.68/1.75  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 4.68/1.75  tff('#skF_5', type, '#skF_5': $i).
% 4.68/1.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.68/1.75  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 4.68/1.75  tff('#skF_6', type, '#skF_6': $i).
% 4.68/1.75  tff('#skF_3', type, '#skF_3': $i).
% 4.68/1.75  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.68/1.75  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.68/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.68/1.75  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.68/1.75  tff('#skF_8', type, '#skF_8': $i).
% 4.68/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.68/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.68/1.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.68/1.75  tff('#skF_4', type, '#skF_4': $i).
% 4.68/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.68/1.75  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.68/1.75  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.68/1.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.68/1.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.68/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.68/1.75  
% 4.68/1.77  tff(f_164, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 4.68/1.77  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.68/1.77  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.68/1.77  tff(f_139, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 4.68/1.77  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.68/1.77  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.68/1.77  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.68/1.77  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.68/1.77  tff(f_115, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 4.68/1.77  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.68/1.77  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.68/1.77  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.68/1.77  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 4.68/1.77  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.68/1.77  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.68/1.77  tff(f_72, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.68/1.77  tff(c_68, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.68/1.77  tff(c_56, plain, (m1_subset_1('#skF_8', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.68/1.77  tff(c_60, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.68/1.77  tff(c_58, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.68/1.77  tff(c_375, plain, (![A_128, B_129, C_130]: (k1_relset_1(A_128, B_129, C_130)=k1_relat_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.68/1.77  tff(c_382, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_58, c_375])).
% 4.68/1.77  tff(c_62, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.68/1.77  tff(c_299, plain, (![A_117, B_118, C_119]: (k2_relset_1(A_117, B_118, C_119)=k2_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.68/1.77  tff(c_307, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_299])).
% 4.68/1.77  tff(c_54, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.68/1.77  tff(c_312, plain, (r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_307, c_54])).
% 4.68/1.77  tff(c_385, plain, (r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_382, c_312])).
% 4.68/1.77  tff(c_52, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.68/1.77  tff(c_66, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.68/1.77  tff(c_64, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.68/1.77  tff(c_1351, plain, (![A_235, D_238, B_236, F_240, E_237, C_239]: (k1_funct_1(k8_funct_2(B_236, C_239, A_235, D_238, E_237), F_240)=k1_funct_1(E_237, k1_funct_1(D_238, F_240)) | k1_xboole_0=B_236 | ~r1_tarski(k2_relset_1(B_236, C_239, D_238), k1_relset_1(C_239, A_235, E_237)) | ~m1_subset_1(F_240, B_236) | ~m1_subset_1(E_237, k1_zfmisc_1(k2_zfmisc_1(C_239, A_235))) | ~v1_funct_1(E_237) | ~m1_subset_1(D_238, k1_zfmisc_1(k2_zfmisc_1(B_236, C_239))) | ~v1_funct_2(D_238, B_236, C_239) | ~v1_funct_1(D_238) | v1_xboole_0(C_239))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.68/1.77  tff(c_1357, plain, (![A_235, E_237, F_240]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', A_235, '#skF_6', E_237), F_240)=k1_funct_1(E_237, k1_funct_1('#skF_6', F_240)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', A_235, E_237)) | ~m1_subset_1(F_240, '#skF_4') | ~m1_subset_1(E_237, k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_235))) | ~v1_funct_1(E_237) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_307, c_1351])).
% 4.68/1.77  tff(c_1369, plain, (![A_235, E_237, F_240]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', A_235, '#skF_6', E_237), F_240)=k1_funct_1(E_237, k1_funct_1('#skF_6', F_240)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', A_235, E_237)) | ~m1_subset_1(F_240, '#skF_4') | ~m1_subset_1(E_237, k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_235))) | ~v1_funct_1(E_237) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_1357])).
% 4.68/1.77  tff(c_1388, plain, (![A_244, E_245, F_246]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', A_244, '#skF_6', E_245), F_246)=k1_funct_1(E_245, k1_funct_1('#skF_6', F_246)) | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', A_244, E_245)) | ~m1_subset_1(F_246, '#skF_4') | ~m1_subset_1(E_245, k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_244))) | ~v1_funct_1(E_245))), inference(negUnitSimplification, [status(thm)], [c_68, c_52, c_1369])).
% 4.68/1.77  tff(c_1390, plain, (![F_246]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_246)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_246)) | ~r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7')) | ~m1_subset_1(F_246, '#skF_4') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_382, c_1388])).
% 4.68/1.77  tff(c_1395, plain, (![F_246]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_246)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_246)) | ~m1_subset_1(F_246, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_385, c_1390])).
% 4.68/1.77  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.68/1.77  tff(c_20, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.68/1.77  tff(c_130, plain, (![B_86, A_87]: (v1_relat_1(B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(A_87)) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.68/1.77  tff(c_136, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_62, c_130])).
% 4.68/1.77  tff(c_142, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_136])).
% 4.68/1.77  tff(c_383, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_375])).
% 4.68/1.77  tff(c_1216, plain, (![B_224, A_225, C_226]: (k1_xboole_0=B_224 | k1_relset_1(A_225, B_224, C_226)=A_225 | ~v1_funct_2(C_226, A_225, B_224) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(A_225, B_224))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.68/1.77  tff(c_1222, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_62, c_1216])).
% 4.68/1.77  tff(c_1228, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_383, c_1222])).
% 4.68/1.77  tff(c_1229, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_1228])).
% 4.68/1.77  tff(c_46, plain, (![A_35, B_36, C_38]: (k7_partfun1(A_35, B_36, C_38)=k1_funct_1(B_36, C_38) | ~r2_hidden(C_38, k1_relat_1(B_36)) | ~v1_funct_1(B_36) | ~v5_relat_1(B_36, A_35) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.68/1.77  tff(c_1277, plain, (![A_35, C_38]: (k7_partfun1(A_35, '#skF_6', C_38)=k1_funct_1('#skF_6', C_38) | ~r2_hidden(C_38, '#skF_4') | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_35) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1229, c_46])).
% 4.68/1.77  tff(c_1307, plain, (![A_230, C_231]: (k7_partfun1(A_230, '#skF_6', C_231)=k1_funct_1('#skF_6', C_231) | ~r2_hidden(C_231, '#skF_4') | ~v5_relat_1('#skF_6', A_230))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_66, c_1277])).
% 4.68/1.77  tff(c_1335, plain, (![A_230]: (k7_partfun1(A_230, '#skF_6', '#skF_1'('#skF_4'))=k1_funct_1('#skF_6', '#skF_1'('#skF_4')) | ~v5_relat_1('#skF_6', A_230) | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_4, c_1307])).
% 4.68/1.77  tff(c_1341, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1335])).
% 4.68/1.77  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.68/1.77  tff(c_1344, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1341, c_12])).
% 4.68/1.77  tff(c_1348, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1344])).
% 4.68/1.77  tff(c_1350, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_1335])).
% 4.68/1.77  tff(c_16, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.68/1.77  tff(c_143, plain, (![C_88, B_89, A_90]: (v5_relat_1(C_88, B_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_90, B_89))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.68/1.77  tff(c_150, plain, (v5_relat_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_143])).
% 4.68/1.77  tff(c_133, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_58, c_130])).
% 4.68/1.77  tff(c_139, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_133])).
% 4.68/1.77  tff(c_836, plain, (![B_181, A_182]: (r2_hidden(k1_funct_1(B_181, A_182), k2_relat_1(B_181)) | ~r2_hidden(A_182, k1_relat_1(B_181)) | ~v1_funct_1(B_181) | ~v1_relat_1(B_181))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.68/1.77  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.68/1.77  tff(c_1421, plain, (![B_249, A_250, B_251]: (r2_hidden(k1_funct_1(B_249, A_250), B_251) | ~r1_tarski(k2_relat_1(B_249), B_251) | ~r2_hidden(A_250, k1_relat_1(B_249)) | ~v1_funct_1(B_249) | ~v1_relat_1(B_249))), inference(resolution, [status(thm)], [c_836, c_6])).
% 4.68/1.77  tff(c_2220, plain, (![A_346, B_347, B_348, A_349]: (k7_partfun1(A_346, B_347, k1_funct_1(B_348, A_349))=k1_funct_1(B_347, k1_funct_1(B_348, A_349)) | ~v1_funct_1(B_347) | ~v5_relat_1(B_347, A_346) | ~v1_relat_1(B_347) | ~r1_tarski(k2_relat_1(B_348), k1_relat_1(B_347)) | ~r2_hidden(A_349, k1_relat_1(B_348)) | ~v1_funct_1(B_348) | ~v1_relat_1(B_348))), inference(resolution, [status(thm)], [c_1421, c_46])).
% 4.68/1.77  tff(c_2224, plain, (![A_346, A_349]: (k7_partfun1(A_346, '#skF_7', k1_funct_1('#skF_6', A_349))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_349)) | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_346) | ~v1_relat_1('#skF_7') | ~r2_hidden(A_349, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_385, c_2220])).
% 4.68/1.77  tff(c_2234, plain, (![A_350, A_351]: (k7_partfun1(A_350, '#skF_7', k1_funct_1('#skF_6', A_351))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', A_351)) | ~v5_relat_1('#skF_7', A_350) | ~r2_hidden(A_351, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_66, c_1229, c_139, c_60, c_2224])).
% 4.68/1.77  tff(c_50, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))!=k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.68/1.77  tff(c_2240, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~v5_relat_1('#skF_7', '#skF_3') | ~r2_hidden('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2234, c_50])).
% 4.68/1.77  tff(c_2246, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~r2_hidden('#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_2240])).
% 4.68/1.77  tff(c_2248, plain, (~r2_hidden('#skF_8', '#skF_4')), inference(splitLeft, [status(thm)], [c_2246])).
% 4.68/1.77  tff(c_2251, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_8', '#skF_4')), inference(resolution, [status(thm)], [c_16, c_2248])).
% 4.68/1.77  tff(c_2254, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2251])).
% 4.68/1.77  tff(c_2256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1350, c_2254])).
% 4.68/1.77  tff(c_2257, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_2246])).
% 4.68/1.77  tff(c_2381, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1395, c_2257])).
% 4.68/1.77  tff(c_2385, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_2381])).
% 4.68/1.77  tff(c_2386, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1228])).
% 4.68/1.77  tff(c_14, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.68/1.77  tff(c_78, plain, (![B_74, A_75]: (~r1_tarski(B_74, A_75) | ~r2_hidden(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.68/1.77  tff(c_83, plain, (![A_76]: (~r1_tarski(A_76, '#skF_1'(A_76)) | v1_xboole_0(A_76))), inference(resolution, [status(thm)], [c_4, c_78])).
% 4.68/1.77  tff(c_88, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_83])).
% 4.68/1.77  tff(c_2397, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2386, c_88])).
% 4.68/1.77  tff(c_2402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_2397])).
% 4.68/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.77  
% 4.68/1.77  Inference rules
% 4.68/1.77  ----------------------
% 4.68/1.77  #Ref     : 0
% 4.68/1.77  #Sup     : 490
% 4.68/1.77  #Fact    : 0
% 4.68/1.77  #Define  : 0
% 4.68/1.77  #Split   : 21
% 4.68/1.77  #Chain   : 0
% 4.68/1.77  #Close   : 0
% 4.68/1.77  
% 4.68/1.77  Ordering : KBO
% 4.68/1.77  
% 4.68/1.77  Simplification rules
% 4.68/1.77  ----------------------
% 4.68/1.77  #Subsume      : 227
% 4.68/1.77  #Demod        : 349
% 4.68/1.77  #Tautology    : 95
% 4.68/1.77  #SimpNegUnit  : 28
% 4.68/1.77  #BackRed      : 43
% 4.68/1.77  
% 4.68/1.77  #Partial instantiations: 0
% 4.68/1.77  #Strategies tried      : 1
% 4.68/1.77  
% 4.68/1.77  Timing (in seconds)
% 4.68/1.77  ----------------------
% 4.68/1.78  Preprocessing        : 0.35
% 4.68/1.78  Parsing              : 0.19
% 4.68/1.78  CNF conversion       : 0.03
% 4.68/1.78  Main loop            : 0.72
% 4.68/1.78  Inferencing          : 0.23
% 4.68/1.78  Reduction            : 0.22
% 4.68/1.78  Demodulation         : 0.15
% 4.68/1.78  BG Simplification    : 0.03
% 4.68/1.78  Subsumption          : 0.18
% 4.68/1.78  Abstraction          : 0.03
% 4.68/1.78  MUC search           : 0.00
% 4.68/1.78  Cooper               : 0.00
% 4.68/1.78  Total                : 1.11
% 4.68/1.78  Index Insertion      : 0.00
% 4.68/1.78  Index Deletion       : 0.00
% 4.68/1.78  Index Matching       : 0.00
% 4.68/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
