%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:41 EST 2020

% Result     : Theorem 4.88s
% Output     : CNFRefutation 5.15s
% Verified   : 
% Statistics : Number of formulae       :  171 (1323 expanded)
%              Number of leaves         :   32 ( 439 expanded)
%              Depth                    :   16
%              Number of atoms          :  327 (3940 expanded)
%              Number of equality atoms :  137 (1071 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_125,negated_conjecture,(
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

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

tff(f_76,axiom,(
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

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_118,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_127,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_118])).

tff(c_137,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_127])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_52,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_458,plain,(
    ! [A_103,B_104,C_105,D_106] :
      ( r2_relset_1(A_103,B_104,C_105,C_105)
      | ~ m1_subset_1(D_106,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_478,plain,(
    ! [C_107] :
      ( r2_relset_1('#skF_2','#skF_3',C_107,C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_56,c_458])).

tff(c_490,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_478])).

tff(c_228,plain,(
    ! [A_71,B_72,C_73] :
      ( k1_relset_1(A_71,B_72,C_73) = k1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_251,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_228])).

tff(c_534,plain,(
    ! [B_114,A_115,C_116] :
      ( k1_xboole_0 = B_114
      | k1_relset_1(A_115,B_114,C_116) = A_115
      | ~ v1_funct_2(C_116,A_115,B_114)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_115,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_544,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_534])).

tff(c_561,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_251,c_544])).

tff(c_571,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_561])).

tff(c_124,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_118])).

tff(c_134,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_124])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_250,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_228])).

tff(c_541,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_534])).

tff(c_558,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_250,c_541])).

tff(c_565,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_558])).

tff(c_614,plain,(
    ! [A_123,B_124] :
      ( r2_hidden('#skF_1'(A_123,B_124),k1_relat_1(A_123))
      | B_124 = A_123
      | k1_relat_1(B_124) != k1_relat_1(A_123)
      | ~ v1_funct_1(B_124)
      | ~ v1_relat_1(B_124)
      | ~ v1_funct_1(A_123)
      | ~ v1_relat_1(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_622,plain,(
    ! [B_124] :
      ( r2_hidden('#skF_1'('#skF_4',B_124),'#skF_2')
      | B_124 = '#skF_4'
      | k1_relat_1(B_124) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_124)
      | ~ v1_relat_1(B_124)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_565,c_614])).

tff(c_661,plain,(
    ! [B_132] :
      ( r2_hidden('#skF_1'('#skF_4',B_132),'#skF_2')
      | B_132 = '#skF_4'
      | k1_relat_1(B_132) != '#skF_2'
      | ~ v1_funct_1(B_132)
      | ~ v1_relat_1(B_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_60,c_565,c_622])).

tff(c_48,plain,(
    ! [E_36] :
      ( k1_funct_1('#skF_5',E_36) = k1_funct_1('#skF_4',E_36)
      | ~ r2_hidden(E_36,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1043,plain,(
    ! [B_160] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_160)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_160))
      | B_160 = '#skF_4'
      | k1_relat_1(B_160) != '#skF_2'
      | ~ v1_funct_1(B_160)
      | ~ v1_relat_1(B_160) ) ),
    inference(resolution,[status(thm)],[c_661,c_48])).

tff(c_26,plain,(
    ! [B_20,A_16] :
      ( k1_funct_1(B_20,'#skF_1'(A_16,B_20)) != k1_funct_1(A_16,'#skF_1'(A_16,B_20))
      | B_20 = A_16
      | k1_relat_1(B_20) != k1_relat_1(A_16)
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1050,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1043,c_26])).

tff(c_1057,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_54,c_571,c_134,c_60,c_571,c_565,c_1050])).

tff(c_46,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1073,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1057,c_46])).

tff(c_1084,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_1073])).

tff(c_1085,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_561])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_99,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_115,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_14,c_99])).

tff(c_1105,plain,(
    ! [A_5] : r1_tarski('#skF_3',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1085,c_115])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1110,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1085,c_1085,c_10])).

tff(c_113,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_99])).

tff(c_162,plain,(
    ! [B_54,A_55] :
      ( B_54 = A_55
      | ~ r1_tarski(B_54,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_172,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_113,c_162])).

tff(c_203,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_1146,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1110,c_203])).

tff(c_1154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1105,c_1146])).

tff(c_1155,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_558])).

tff(c_1175,plain,(
    ! [A_5] : r1_tarski('#skF_3',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1155,c_115])).

tff(c_1180,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1155,c_1155,c_10])).

tff(c_1257,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1180,c_203])).

tff(c_1265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1175,c_1257])).

tff(c_1266,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_1272,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1266,c_50])).

tff(c_1341,plain,(
    ! [A_181,B_182,C_183] :
      ( k1_relset_1(A_181,B_182,C_183) = k1_relat_1(C_183)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1407,plain,(
    ! [C_194] :
      ( k1_relset_1('#skF_2','#skF_3',C_194) = k1_relat_1(C_194)
      | ~ m1_subset_1(C_194,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1266,c_1341])).

tff(c_1422,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1272,c_1407])).

tff(c_1676,plain,(
    ! [B_236,A_237,C_238] :
      ( k1_xboole_0 = B_236
      | k1_relset_1(A_237,B_236,C_238) = A_237
      | ~ v1_funct_2(C_238,A_237,B_236)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_237,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1679,plain,(
    ! [C_238] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1('#skF_2','#skF_3',C_238) = '#skF_2'
      | ~ v1_funct_2(C_238,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_238,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1266,c_1676])).

tff(c_1716,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1679])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1277,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1266,c_8])).

tff(c_1331,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1277])).

tff(c_1736,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1716,c_1331])).

tff(c_1809,plain,(
    ! [A_245] : k2_zfmisc_1(A_245,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1716,c_1716,c_10])).

tff(c_1832,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1809,c_1266])).

tff(c_1844,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1736,c_1832])).

tff(c_1880,plain,(
    ! [C_248] :
      ( k1_relset_1('#skF_2','#skF_3',C_248) = '#skF_2'
      | ~ v1_funct_2(C_248,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_248,k1_zfmisc_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_1679])).

tff(c_1883,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_1272,c_1880])).

tff(c_1897,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1422,c_1883])).

tff(c_1271,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1266,c_56])).

tff(c_1423,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1271,c_1407])).

tff(c_1886,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_1271,c_1880])).

tff(c_1900,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1423,c_1886])).

tff(c_28,plain,(
    ! [A_16,B_20] :
      ( r2_hidden('#skF_1'(A_16,B_20),k1_relat_1(A_16))
      | B_20 = A_16
      | k1_relat_1(B_20) != k1_relat_1(A_16)
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1923,plain,(
    ! [B_20] :
      ( r2_hidden('#skF_1'('#skF_4',B_20),'#skF_2')
      | B_20 = '#skF_4'
      | k1_relat_1(B_20) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1900,c_28])).

tff(c_1973,plain,(
    ! [B_252] :
      ( r2_hidden('#skF_1'('#skF_4',B_252),'#skF_2')
      | B_252 = '#skF_4'
      | k1_relat_1(B_252) != '#skF_2'
      | ~ v1_funct_1(B_252)
      | ~ v1_relat_1(B_252) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_60,c_1900,c_1923])).

tff(c_2384,plain,(
    ! [B_279] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_279)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_279))
      | B_279 = '#skF_4'
      | k1_relat_1(B_279) != '#skF_2'
      | ~ v1_funct_1(B_279)
      | ~ v1_relat_1(B_279) ) ),
    inference(resolution,[status(thm)],[c_1973,c_48])).

tff(c_2391,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2384,c_26])).

tff(c_2398,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_54,c_1897,c_134,c_60,c_1900,c_1897,c_2391])).

tff(c_114,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_99])).

tff(c_171,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_114,c_162])).

tff(c_202,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_171])).

tff(c_1268,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1266,c_202])).

tff(c_2409,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2398,c_1268])).

tff(c_2422,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2409])).

tff(c_2424,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1277])).

tff(c_2428,plain,(
    ! [A_5] : r1_tarski('#skF_4',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2424,c_115])).

tff(c_2441,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2428,c_1268])).

tff(c_2442,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_2447,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2442,c_50])).

tff(c_2518,plain,(
    ! [A_292,B_293,C_294] :
      ( k1_relset_1(A_292,B_293,C_294) = k1_relat_1(C_294)
      | ~ m1_subset_1(C_294,k1_zfmisc_1(k2_zfmisc_1(A_292,B_293))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2598,plain,(
    ! [C_307] :
      ( k1_relset_1('#skF_2','#skF_3',C_307) = k1_relat_1(C_307)
      | ~ m1_subset_1(C_307,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2442,c_2518])).

tff(c_2613,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2447,c_2598])).

tff(c_2703,plain,(
    ! [B_318,C_319,A_320] :
      ( k1_xboole_0 = B_318
      | v1_funct_2(C_319,A_320,B_318)
      | k1_relset_1(A_320,B_318,C_319) != A_320
      | ~ m1_subset_1(C_319,k1_zfmisc_1(k2_zfmisc_1(A_320,B_318))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2706,plain,(
    ! [C_319] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2(C_319,'#skF_2','#skF_3')
      | k1_relset_1('#skF_2','#skF_3',C_319) != '#skF_2'
      | ~ m1_subset_1(C_319,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2442,c_2703])).

tff(c_2741,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2706])).

tff(c_2452,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2442,c_8])).

tff(c_2507,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2452])).

tff(c_2754,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2741,c_2507])).

tff(c_2763,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2741,c_2741,c_10])).

tff(c_2787,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2763,c_2442])).

tff(c_2789,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2754,c_2787])).

tff(c_2791,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2706])).

tff(c_2853,plain,(
    ! [B_339,A_340,C_341] :
      ( k1_xboole_0 = B_339
      | k1_relset_1(A_340,B_339,C_341) = A_340
      | ~ v1_funct_2(C_341,A_340,B_339)
      | ~ m1_subset_1(C_341,k1_zfmisc_1(k2_zfmisc_1(A_340,B_339))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2856,plain,(
    ! [C_341] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1('#skF_2','#skF_3',C_341) = '#skF_2'
      | ~ v1_funct_2(C_341,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_341,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2442,c_2853])).

tff(c_2982,plain,(
    ! [C_357] :
      ( k1_relset_1('#skF_2','#skF_3',C_357) = '#skF_2'
      | ~ v1_funct_2(C_357,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_357,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2791,c_2856])).

tff(c_2985,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_2447,c_2982])).

tff(c_2999,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2613,c_2985])).

tff(c_2446,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2442,c_56])).

tff(c_2614,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2446,c_2598])).

tff(c_2988,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_2446,c_2982])).

tff(c_3002,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2614,c_2988])).

tff(c_3021,plain,(
    ! [B_20] :
      ( r2_hidden('#skF_1'('#skF_4',B_20),'#skF_2')
      | B_20 = '#skF_4'
      | k1_relat_1(B_20) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3002,c_28])).

tff(c_3085,plain,(
    ! [B_362] :
      ( r2_hidden('#skF_1'('#skF_4',B_362),'#skF_2')
      | B_362 = '#skF_4'
      | k1_relat_1(B_362) != '#skF_2'
      | ~ v1_funct_1(B_362)
      | ~ v1_relat_1(B_362) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_60,c_3002,c_3021])).

tff(c_3093,plain,(
    ! [B_363] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_363)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_363))
      | B_363 = '#skF_4'
      | k1_relat_1(B_363) != '#skF_2'
      | ~ v1_funct_1(B_363)
      | ~ v1_relat_1(B_363) ) ),
    inference(resolution,[status(thm)],[c_3085,c_48])).

tff(c_3100,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3093,c_26])).

tff(c_3107,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_54,c_2999,c_134,c_60,c_3002,c_2999,c_3100])).

tff(c_2445,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2442,c_113])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2464,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2445,c_2])).

tff(c_2505,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2464])).

tff(c_3124,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3107,c_2505])).

tff(c_3140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3124])).

tff(c_3142,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2452])).

tff(c_3146,plain,(
    ! [A_5] : r1_tarski('#skF_5',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3142,c_115])).

tff(c_3159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3146,c_2505])).

tff(c_3160,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2464])).

tff(c_3169,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3160,c_46])).

tff(c_3163,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3160,c_3160,c_2447])).

tff(c_3166,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3160,c_2442])).

tff(c_3331,plain,(
    ! [A_389,B_390,C_391,D_392] :
      ( r2_relset_1(A_389,B_390,C_391,C_391)
      | ~ m1_subset_1(D_392,k1_zfmisc_1(k2_zfmisc_1(A_389,B_390)))
      | ~ m1_subset_1(C_391,k1_zfmisc_1(k2_zfmisc_1(A_389,B_390))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3390,plain,(
    ! [A_398,B_399,C_400] :
      ( r2_relset_1(A_398,B_399,C_400,C_400)
      | ~ m1_subset_1(C_400,k1_zfmisc_1(k2_zfmisc_1(A_398,B_399))) ) ),
    inference(resolution,[status(thm)],[c_14,c_3331])).

tff(c_3428,plain,(
    ! [C_409] :
      ( r2_relset_1('#skF_2','#skF_3',C_409,C_409)
      | ~ m1_subset_1(C_409,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3166,c_3390])).

tff(c_3430,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_3163,c_3428])).

tff(c_3440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3169,c_3430])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:16:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.88/1.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.15/1.98  
% 5.15/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.15/1.99  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.15/1.99  
% 5.15/1.99  %Foreground sorts:
% 5.15/1.99  
% 5.15/1.99  
% 5.15/1.99  %Background operators:
% 5.15/1.99  
% 5.15/1.99  
% 5.15/1.99  %Foreground operators:
% 5.15/1.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.15/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.15/1.99  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.15/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.15/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.15/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.15/1.99  tff('#skF_5', type, '#skF_5': $i).
% 5.15/1.99  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.15/1.99  tff('#skF_2', type, '#skF_2': $i).
% 5.15/1.99  tff('#skF_3', type, '#skF_3': $i).
% 5.15/1.99  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.15/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.15/1.99  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.15/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.15/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.15/1.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.15/1.99  tff('#skF_4', type, '#skF_4': $i).
% 5.15/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.15/1.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.15/1.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.15/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.15/1.99  
% 5.15/2.01  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.15/2.01  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.15/2.01  tff(f_125, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 5.15/2.01  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.15/2.01  tff(f_86, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.15/2.01  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.15/2.01  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.15/2.01  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 5.15/2.01  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.15/2.01  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.15/2.01  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.15/2.01  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.15/2.01  tff(c_24, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.15/2.01  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.15/2.01  tff(c_118, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.15/2.01  tff(c_127, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_118])).
% 5.15/2.01  tff(c_137, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_127])).
% 5.15/2.01  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.15/2.01  tff(c_52, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.15/2.01  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.15/2.01  tff(c_458, plain, (![A_103, B_104, C_105, D_106]: (r2_relset_1(A_103, B_104, C_105, C_105) | ~m1_subset_1(D_106, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.15/2.01  tff(c_478, plain, (![C_107]: (r2_relset_1('#skF_2', '#skF_3', C_107, C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_56, c_458])).
% 5.15/2.01  tff(c_490, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_478])).
% 5.15/2.01  tff(c_228, plain, (![A_71, B_72, C_73]: (k1_relset_1(A_71, B_72, C_73)=k1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.15/2.01  tff(c_251, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_228])).
% 5.15/2.01  tff(c_534, plain, (![B_114, A_115, C_116]: (k1_xboole_0=B_114 | k1_relset_1(A_115, B_114, C_116)=A_115 | ~v1_funct_2(C_116, A_115, B_114) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_115, B_114))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.15/2.01  tff(c_544, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_534])).
% 5.15/2.01  tff(c_561, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_251, c_544])).
% 5.15/2.01  tff(c_571, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_561])).
% 5.15/2.01  tff(c_124, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_56, c_118])).
% 5.15/2.01  tff(c_134, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_124])).
% 5.15/2.01  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.15/2.01  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.15/2.01  tff(c_250, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_228])).
% 5.15/2.01  tff(c_541, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_534])).
% 5.15/2.01  tff(c_558, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_250, c_541])).
% 5.15/2.01  tff(c_565, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_558])).
% 5.15/2.01  tff(c_614, plain, (![A_123, B_124]: (r2_hidden('#skF_1'(A_123, B_124), k1_relat_1(A_123)) | B_124=A_123 | k1_relat_1(B_124)!=k1_relat_1(A_123) | ~v1_funct_1(B_124) | ~v1_relat_1(B_124) | ~v1_funct_1(A_123) | ~v1_relat_1(A_123))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.15/2.01  tff(c_622, plain, (![B_124]: (r2_hidden('#skF_1'('#skF_4', B_124), '#skF_2') | B_124='#skF_4' | k1_relat_1(B_124)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_124) | ~v1_relat_1(B_124) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_565, c_614])).
% 5.15/2.01  tff(c_661, plain, (![B_132]: (r2_hidden('#skF_1'('#skF_4', B_132), '#skF_2') | B_132='#skF_4' | k1_relat_1(B_132)!='#skF_2' | ~v1_funct_1(B_132) | ~v1_relat_1(B_132))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_60, c_565, c_622])).
% 5.15/2.01  tff(c_48, plain, (![E_36]: (k1_funct_1('#skF_5', E_36)=k1_funct_1('#skF_4', E_36) | ~r2_hidden(E_36, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.15/2.01  tff(c_1043, plain, (![B_160]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_160))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_160)) | B_160='#skF_4' | k1_relat_1(B_160)!='#skF_2' | ~v1_funct_1(B_160) | ~v1_relat_1(B_160))), inference(resolution, [status(thm)], [c_661, c_48])).
% 5.15/2.01  tff(c_26, plain, (![B_20, A_16]: (k1_funct_1(B_20, '#skF_1'(A_16, B_20))!=k1_funct_1(A_16, '#skF_1'(A_16, B_20)) | B_20=A_16 | k1_relat_1(B_20)!=k1_relat_1(A_16) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.15/2.01  tff(c_1050, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1043, c_26])).
% 5.15/2.01  tff(c_1057, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_137, c_54, c_571, c_134, c_60, c_571, c_565, c_1050])).
% 5.15/2.01  tff(c_46, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.15/2.01  tff(c_1073, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1057, c_46])).
% 5.15/2.01  tff(c_1084, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_490, c_1073])).
% 5.15/2.01  tff(c_1085, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_561])).
% 5.15/2.01  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.15/2.01  tff(c_99, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.15/2.01  tff(c_115, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_14, c_99])).
% 5.15/2.01  tff(c_1105, plain, (![A_5]: (r1_tarski('#skF_3', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_1085, c_115])).
% 5.15/2.01  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.15/2.01  tff(c_1110, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1085, c_1085, c_10])).
% 5.15/2.01  tff(c_113, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_56, c_99])).
% 5.15/2.01  tff(c_162, plain, (![B_54, A_55]: (B_54=A_55 | ~r1_tarski(B_54, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.15/2.01  tff(c_172, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_113, c_162])).
% 5.15/2.01  tff(c_203, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_172])).
% 5.15/2.01  tff(c_1146, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1110, c_203])).
% 5.15/2.01  tff(c_1154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1105, c_1146])).
% 5.15/2.01  tff(c_1155, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_558])).
% 5.15/2.01  tff(c_1175, plain, (![A_5]: (r1_tarski('#skF_3', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_1155, c_115])).
% 5.15/2.01  tff(c_1180, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1155, c_1155, c_10])).
% 5.15/2.01  tff(c_1257, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1180, c_203])).
% 5.15/2.01  tff(c_1265, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1175, c_1257])).
% 5.15/2.01  tff(c_1266, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_172])).
% 5.15/2.01  tff(c_1272, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1266, c_50])).
% 5.15/2.01  tff(c_1341, plain, (![A_181, B_182, C_183]: (k1_relset_1(A_181, B_182, C_183)=k1_relat_1(C_183) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.15/2.01  tff(c_1407, plain, (![C_194]: (k1_relset_1('#skF_2', '#skF_3', C_194)=k1_relat_1(C_194) | ~m1_subset_1(C_194, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1266, c_1341])).
% 5.15/2.01  tff(c_1422, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1272, c_1407])).
% 5.15/2.01  tff(c_1676, plain, (![B_236, A_237, C_238]: (k1_xboole_0=B_236 | k1_relset_1(A_237, B_236, C_238)=A_237 | ~v1_funct_2(C_238, A_237, B_236) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_237, B_236))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.15/2.01  tff(c_1679, plain, (![C_238]: (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', C_238)='#skF_2' | ~v1_funct_2(C_238, '#skF_2', '#skF_3') | ~m1_subset_1(C_238, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1266, c_1676])).
% 5.15/2.01  tff(c_1716, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1679])).
% 5.15/2.01  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.15/2.01  tff(c_1277, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1266, c_8])).
% 5.15/2.01  tff(c_1331, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_1277])).
% 5.15/2.01  tff(c_1736, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1716, c_1331])).
% 5.15/2.01  tff(c_1809, plain, (![A_245]: (k2_zfmisc_1(A_245, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1716, c_1716, c_10])).
% 5.15/2.01  tff(c_1832, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1809, c_1266])).
% 5.15/2.01  tff(c_1844, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1736, c_1832])).
% 5.15/2.01  tff(c_1880, plain, (![C_248]: (k1_relset_1('#skF_2', '#skF_3', C_248)='#skF_2' | ~v1_funct_2(C_248, '#skF_2', '#skF_3') | ~m1_subset_1(C_248, k1_zfmisc_1('#skF_4')))), inference(splitRight, [status(thm)], [c_1679])).
% 5.15/2.01  tff(c_1883, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_1272, c_1880])).
% 5.15/2.01  tff(c_1897, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1422, c_1883])).
% 5.15/2.01  tff(c_1271, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1266, c_56])).
% 5.15/2.01  tff(c_1423, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1271, c_1407])).
% 5.15/2.01  tff(c_1886, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_1271, c_1880])).
% 5.15/2.01  tff(c_1900, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1423, c_1886])).
% 5.15/2.01  tff(c_28, plain, (![A_16, B_20]: (r2_hidden('#skF_1'(A_16, B_20), k1_relat_1(A_16)) | B_20=A_16 | k1_relat_1(B_20)!=k1_relat_1(A_16) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.15/2.01  tff(c_1923, plain, (![B_20]: (r2_hidden('#skF_1'('#skF_4', B_20), '#skF_2') | B_20='#skF_4' | k1_relat_1(B_20)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_20) | ~v1_relat_1(B_20) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1900, c_28])).
% 5.15/2.01  tff(c_1973, plain, (![B_252]: (r2_hidden('#skF_1'('#skF_4', B_252), '#skF_2') | B_252='#skF_4' | k1_relat_1(B_252)!='#skF_2' | ~v1_funct_1(B_252) | ~v1_relat_1(B_252))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_60, c_1900, c_1923])).
% 5.15/2.01  tff(c_2384, plain, (![B_279]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_279))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_279)) | B_279='#skF_4' | k1_relat_1(B_279)!='#skF_2' | ~v1_funct_1(B_279) | ~v1_relat_1(B_279))), inference(resolution, [status(thm)], [c_1973, c_48])).
% 5.15/2.01  tff(c_2391, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2384, c_26])).
% 5.15/2.01  tff(c_2398, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_137, c_54, c_1897, c_134, c_60, c_1900, c_1897, c_2391])).
% 5.15/2.01  tff(c_114, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_99])).
% 5.15/2.01  tff(c_171, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_114, c_162])).
% 5.15/2.01  tff(c_202, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_171])).
% 5.15/2.01  tff(c_1268, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1266, c_202])).
% 5.15/2.01  tff(c_2409, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2398, c_1268])).
% 5.15/2.01  tff(c_2422, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2409])).
% 5.15/2.01  tff(c_2424, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1277])).
% 5.15/2.01  tff(c_2428, plain, (![A_5]: (r1_tarski('#skF_4', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_2424, c_115])).
% 5.15/2.01  tff(c_2441, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2428, c_1268])).
% 5.15/2.01  tff(c_2442, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5'), inference(splitRight, [status(thm)], [c_171])).
% 5.15/2.01  tff(c_2447, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2442, c_50])).
% 5.15/2.01  tff(c_2518, plain, (![A_292, B_293, C_294]: (k1_relset_1(A_292, B_293, C_294)=k1_relat_1(C_294) | ~m1_subset_1(C_294, k1_zfmisc_1(k2_zfmisc_1(A_292, B_293))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.15/2.01  tff(c_2598, plain, (![C_307]: (k1_relset_1('#skF_2', '#skF_3', C_307)=k1_relat_1(C_307) | ~m1_subset_1(C_307, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2442, c_2518])).
% 5.15/2.01  tff(c_2613, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2447, c_2598])).
% 5.15/2.01  tff(c_2703, plain, (![B_318, C_319, A_320]: (k1_xboole_0=B_318 | v1_funct_2(C_319, A_320, B_318) | k1_relset_1(A_320, B_318, C_319)!=A_320 | ~m1_subset_1(C_319, k1_zfmisc_1(k2_zfmisc_1(A_320, B_318))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.15/2.01  tff(c_2706, plain, (![C_319]: (k1_xboole_0='#skF_3' | v1_funct_2(C_319, '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', C_319)!='#skF_2' | ~m1_subset_1(C_319, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2442, c_2703])).
% 5.15/2.01  tff(c_2741, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2706])).
% 5.15/2.01  tff(c_2452, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2442, c_8])).
% 5.15/2.01  tff(c_2507, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_2452])).
% 5.15/2.01  tff(c_2754, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2741, c_2507])).
% 5.15/2.01  tff(c_2763, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2741, c_2741, c_10])).
% 5.15/2.01  tff(c_2787, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2763, c_2442])).
% 5.15/2.01  tff(c_2789, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2754, c_2787])).
% 5.15/2.01  tff(c_2791, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_2706])).
% 5.15/2.01  tff(c_2853, plain, (![B_339, A_340, C_341]: (k1_xboole_0=B_339 | k1_relset_1(A_340, B_339, C_341)=A_340 | ~v1_funct_2(C_341, A_340, B_339) | ~m1_subset_1(C_341, k1_zfmisc_1(k2_zfmisc_1(A_340, B_339))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.15/2.01  tff(c_2856, plain, (![C_341]: (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', C_341)='#skF_2' | ~v1_funct_2(C_341, '#skF_2', '#skF_3') | ~m1_subset_1(C_341, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2442, c_2853])).
% 5.15/2.01  tff(c_2982, plain, (![C_357]: (k1_relset_1('#skF_2', '#skF_3', C_357)='#skF_2' | ~v1_funct_2(C_357, '#skF_2', '#skF_3') | ~m1_subset_1(C_357, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_2791, c_2856])).
% 5.15/2.01  tff(c_2985, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_2447, c_2982])).
% 5.15/2.01  tff(c_2999, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2613, c_2985])).
% 5.15/2.01  tff(c_2446, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2442, c_56])).
% 5.15/2.01  tff(c_2614, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2446, c_2598])).
% 5.15/2.01  tff(c_2988, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_2446, c_2982])).
% 5.15/2.01  tff(c_3002, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2614, c_2988])).
% 5.15/2.01  tff(c_3021, plain, (![B_20]: (r2_hidden('#skF_1'('#skF_4', B_20), '#skF_2') | B_20='#skF_4' | k1_relat_1(B_20)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_20) | ~v1_relat_1(B_20) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3002, c_28])).
% 5.15/2.01  tff(c_3085, plain, (![B_362]: (r2_hidden('#skF_1'('#skF_4', B_362), '#skF_2') | B_362='#skF_4' | k1_relat_1(B_362)!='#skF_2' | ~v1_funct_1(B_362) | ~v1_relat_1(B_362))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_60, c_3002, c_3021])).
% 5.15/2.01  tff(c_3093, plain, (![B_363]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_363))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_363)) | B_363='#skF_4' | k1_relat_1(B_363)!='#skF_2' | ~v1_funct_1(B_363) | ~v1_relat_1(B_363))), inference(resolution, [status(thm)], [c_3085, c_48])).
% 5.15/2.01  tff(c_3100, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3093, c_26])).
% 5.15/2.01  tff(c_3107, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_137, c_54, c_2999, c_134, c_60, c_3002, c_2999, c_3100])).
% 5.15/2.01  tff(c_2445, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2442, c_113])).
% 5.15/2.01  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.15/2.01  tff(c_2464, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2445, c_2])).
% 5.15/2.01  tff(c_2505, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_2464])).
% 5.15/2.01  tff(c_3124, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3107, c_2505])).
% 5.15/2.01  tff(c_3140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3124])).
% 5.15/2.01  tff(c_3142, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2452])).
% 5.15/2.01  tff(c_3146, plain, (![A_5]: (r1_tarski('#skF_5', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_3142, c_115])).
% 5.15/2.01  tff(c_3159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3146, c_2505])).
% 5.15/2.01  tff(c_3160, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_2464])).
% 5.15/2.01  tff(c_3169, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3160, c_46])).
% 5.15/2.01  tff(c_3163, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3160, c_3160, c_2447])).
% 5.15/2.01  tff(c_3166, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3160, c_2442])).
% 5.15/2.01  tff(c_3331, plain, (![A_389, B_390, C_391, D_392]: (r2_relset_1(A_389, B_390, C_391, C_391) | ~m1_subset_1(D_392, k1_zfmisc_1(k2_zfmisc_1(A_389, B_390))) | ~m1_subset_1(C_391, k1_zfmisc_1(k2_zfmisc_1(A_389, B_390))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.15/2.01  tff(c_3390, plain, (![A_398, B_399, C_400]: (r2_relset_1(A_398, B_399, C_400, C_400) | ~m1_subset_1(C_400, k1_zfmisc_1(k2_zfmisc_1(A_398, B_399))))), inference(resolution, [status(thm)], [c_14, c_3331])).
% 5.15/2.01  tff(c_3428, plain, (![C_409]: (r2_relset_1('#skF_2', '#skF_3', C_409, C_409) | ~m1_subset_1(C_409, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_3166, c_3390])).
% 5.15/2.01  tff(c_3430, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_3163, c_3428])).
% 5.15/2.01  tff(c_3440, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3169, c_3430])).
% 5.15/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.15/2.01  
% 5.15/2.01  Inference rules
% 5.15/2.01  ----------------------
% 5.15/2.01  #Ref     : 3
% 5.15/2.01  #Sup     : 679
% 5.15/2.01  #Fact    : 0
% 5.15/2.01  #Define  : 0
% 5.15/2.01  #Split   : 18
% 5.15/2.01  #Chain   : 0
% 5.15/2.01  #Close   : 0
% 5.15/2.01  
% 5.15/2.01  Ordering : KBO
% 5.15/2.01  
% 5.15/2.01  Simplification rules
% 5.15/2.01  ----------------------
% 5.15/2.01  #Subsume      : 106
% 5.15/2.01  #Demod        : 829
% 5.15/2.01  #Tautology    : 318
% 5.15/2.01  #SimpNegUnit  : 39
% 5.15/2.01  #BackRed      : 215
% 5.15/2.01  
% 5.15/2.01  #Partial instantiations: 0
% 5.15/2.01  #Strategies tried      : 1
% 5.15/2.01  
% 5.15/2.01  Timing (in seconds)
% 5.15/2.01  ----------------------
% 5.15/2.01  Preprocessing        : 0.36
% 5.15/2.01  Parsing              : 0.19
% 5.15/2.01  CNF conversion       : 0.03
% 5.15/2.01  Main loop            : 0.81
% 5.15/2.01  Inferencing          : 0.27
% 5.15/2.01  Reduction            : 0.28
% 5.15/2.01  Demodulation         : 0.20
% 5.15/2.01  BG Simplification    : 0.04
% 5.15/2.01  Subsumption          : 0.15
% 5.15/2.01  Abstraction          : 0.04
% 5.15/2.01  MUC search           : 0.00
% 5.15/2.01  Cooper               : 0.00
% 5.15/2.01  Total                : 1.22
% 5.15/2.01  Index Insertion      : 0.00
% 5.15/2.01  Index Deletion       : 0.00
% 5.15/2.01  Index Matching       : 0.00
% 5.15/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
