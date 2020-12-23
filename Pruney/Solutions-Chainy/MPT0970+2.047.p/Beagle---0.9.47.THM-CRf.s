%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:25 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 184 expanded)
%              Number of leaves         :   36 (  79 expanded)
%              Depth                    :   11
%              Number of atoms          :  142 ( 469 expanded)
%              Number of equality atoms :   36 ( 123 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_55,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_95,axiom,(
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

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_181,plain,(
    ! [A_77,B_78,C_79] :
      ( k2_relset_1(A_77,B_78,C_79) = k2_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_185,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_181])).

tff(c_46,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_186,plain,(
    k2_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_46])).

tff(c_22,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_102,plain,(
    ! [B_48,A_49] :
      ( v1_relat_1(B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_105,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_102])).

tff(c_108,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_105])).

tff(c_146,plain,(
    ! [C_64,B_65,A_66] :
      ( v5_relat_1(C_64,B_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_66,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_150,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_146])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_50,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_151,plain,(
    ! [A_67,B_68,C_69] :
      ( k1_relset_1(A_67,B_68,C_69) = k1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_155,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_151])).

tff(c_326,plain,(
    ! [B_115,A_116,C_117] :
      ( k1_xboole_0 = B_115
      | k1_relset_1(A_116,B_115,C_117) = A_116
      | ~ v1_funct_2(C_117,A_116,B_115)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_116,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_329,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_326])).

tff(c_332,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_155,c_329])).

tff(c_333,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_332])).

tff(c_56,plain,(
    ! [D_33] :
      ( r2_hidden('#skF_5'(D_33),'#skF_2')
      | ~ r2_hidden(D_33,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_114,plain,(
    ! [C_53,B_54,A_55] :
      ( r2_hidden(C_53,B_54)
      | ~ r2_hidden(C_53,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_120,plain,(
    ! [D_33,B_54] :
      ( r2_hidden('#skF_5'(D_33),B_54)
      | ~ r1_tarski('#skF_2',B_54)
      | ~ r2_hidden(D_33,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_56,c_114])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_54,plain,(
    ! [D_33] :
      ( k1_funct_1('#skF_4','#skF_5'(D_33)) = D_33
      | ~ r2_hidden(D_33,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_209,plain,(
    ! [B_84,A_85] :
      ( r2_hidden(k1_funct_1(B_84,A_85),k2_relat_1(B_84))
      | ~ r2_hidden(A_85,k1_relat_1(B_84))
      | ~ v1_funct_1(B_84)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_214,plain,(
    ! [D_33] :
      ( r2_hidden(D_33,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_5'(D_33),k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ r2_hidden(D_33,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_209])).

tff(c_218,plain,(
    ! [D_86] :
      ( r2_hidden(D_86,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_5'(D_86),k1_relat_1('#skF_4'))
      | ~ r2_hidden(D_86,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_52,c_214])).

tff(c_223,plain,(
    ! [D_33] :
      ( r2_hidden(D_33,k2_relat_1('#skF_4'))
      | ~ r1_tarski('#skF_2',k1_relat_1('#skF_4'))
      | ~ r2_hidden(D_33,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_120,c_218])).

tff(c_224,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_223])).

tff(c_334,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_224])).

tff(c_339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_334])).

tff(c_340,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_332])).

tff(c_132,plain,(
    ! [B_61,A_62] :
      ( r1_tarski(k2_relat_1(B_61),A_62)
      | ~ v5_relat_1(B_61,A_62)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_72,plain,(
    ! [B_43,A_44] :
      ( B_43 = A_44
      | ~ r1_tarski(B_43,A_44)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_81,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_72])).

tff(c_143,plain,(
    ! [B_61] :
      ( k2_relat_1(B_61) = k1_xboole_0
      | ~ v5_relat_1(B_61,k1_xboole_0)
      | ~ v1_relat_1(B_61) ) ),
    inference(resolution,[status(thm)],[c_132,c_81])).

tff(c_416,plain,(
    ! [B_125] :
      ( k2_relat_1(B_125) = '#skF_3'
      | ~ v5_relat_1(B_125,'#skF_3')
      | ~ v1_relat_1(B_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_340,c_143])).

tff(c_419,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_150,c_416])).

tff(c_422,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_419])).

tff(c_424,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_422])).

tff(c_435,plain,(
    ! [D_126] :
      ( r2_hidden(D_126,k2_relat_1('#skF_4'))
      | ~ r2_hidden(D_126,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_450,plain,(
    ! [A_131] :
      ( r1_tarski(A_131,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_131,k2_relat_1('#skF_4')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_435,c_4])).

tff(c_460,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_450])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_144,plain,(
    ! [B_61,A_62] :
      ( k2_relat_1(B_61) = A_62
      | ~ r1_tarski(A_62,k2_relat_1(B_61))
      | ~ v5_relat_1(B_61,A_62)
      | ~ v1_relat_1(B_61) ) ),
    inference(resolution,[status(thm)],[c_132,c_8])).

tff(c_463,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_460,c_144])).

tff(c_470,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_150,c_463])).

tff(c_472,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_470])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:19:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.43  
% 2.77/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.43  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.77/1.43  
% 2.77/1.43  %Foreground sorts:
% 2.77/1.43  
% 2.77/1.43  
% 2.77/1.43  %Background operators:
% 2.77/1.43  
% 2.77/1.43  
% 2.77/1.43  %Foreground operators:
% 2.77/1.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.77/1.43  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.77/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.77/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.77/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.77/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.77/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.77/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.77/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.77/1.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.77/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.77/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.77/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.77/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.77/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.77/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.43  
% 2.77/1.45  tff(f_114, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 2.77/1.45  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.77/1.45  tff(f_55, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.77/1.45  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.77/1.45  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.77/1.45  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.77/1.45  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.77/1.45  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.77/1.45  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.77/1.45  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 2.77/1.45  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.77/1.45  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.77/1.45  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.77/1.45  tff(c_181, plain, (![A_77, B_78, C_79]: (k2_relset_1(A_77, B_78, C_79)=k2_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.77/1.45  tff(c_185, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_181])).
% 2.77/1.45  tff(c_46, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.77/1.45  tff(c_186, plain, (k2_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_185, c_46])).
% 2.77/1.45  tff(c_22, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.77/1.45  tff(c_102, plain, (![B_48, A_49]: (v1_relat_1(B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.77/1.45  tff(c_105, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_102])).
% 2.77/1.45  tff(c_108, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_105])).
% 2.77/1.45  tff(c_146, plain, (![C_64, B_65, A_66]: (v5_relat_1(C_64, B_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_66, B_65))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.77/1.45  tff(c_150, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_146])).
% 2.77/1.45  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.77/1.45  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.77/1.45  tff(c_50, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.77/1.45  tff(c_151, plain, (![A_67, B_68, C_69]: (k1_relset_1(A_67, B_68, C_69)=k1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.77/1.45  tff(c_155, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_151])).
% 2.77/1.45  tff(c_326, plain, (![B_115, A_116, C_117]: (k1_xboole_0=B_115 | k1_relset_1(A_116, B_115, C_117)=A_116 | ~v1_funct_2(C_117, A_116, B_115) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_116, B_115))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.77/1.45  tff(c_329, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_326])).
% 2.77/1.45  tff(c_332, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_155, c_329])).
% 2.77/1.45  tff(c_333, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_332])).
% 2.77/1.45  tff(c_56, plain, (![D_33]: (r2_hidden('#skF_5'(D_33), '#skF_2') | ~r2_hidden(D_33, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.77/1.45  tff(c_114, plain, (![C_53, B_54, A_55]: (r2_hidden(C_53, B_54) | ~r2_hidden(C_53, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.77/1.45  tff(c_120, plain, (![D_33, B_54]: (r2_hidden('#skF_5'(D_33), B_54) | ~r1_tarski('#skF_2', B_54) | ~r2_hidden(D_33, '#skF_3'))), inference(resolution, [status(thm)], [c_56, c_114])).
% 2.77/1.45  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.77/1.45  tff(c_54, plain, (![D_33]: (k1_funct_1('#skF_4', '#skF_5'(D_33))=D_33 | ~r2_hidden(D_33, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.77/1.45  tff(c_209, plain, (![B_84, A_85]: (r2_hidden(k1_funct_1(B_84, A_85), k2_relat_1(B_84)) | ~r2_hidden(A_85, k1_relat_1(B_84)) | ~v1_funct_1(B_84) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.77/1.45  tff(c_214, plain, (![D_33]: (r2_hidden(D_33, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_5'(D_33), k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r2_hidden(D_33, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_209])).
% 2.77/1.45  tff(c_218, plain, (![D_86]: (r2_hidden(D_86, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_5'(D_86), k1_relat_1('#skF_4')) | ~r2_hidden(D_86, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_52, c_214])).
% 2.77/1.45  tff(c_223, plain, (![D_33]: (r2_hidden(D_33, k2_relat_1('#skF_4')) | ~r1_tarski('#skF_2', k1_relat_1('#skF_4')) | ~r2_hidden(D_33, '#skF_3'))), inference(resolution, [status(thm)], [c_120, c_218])).
% 2.77/1.45  tff(c_224, plain, (~r1_tarski('#skF_2', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_223])).
% 2.77/1.45  tff(c_334, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_333, c_224])).
% 2.77/1.45  tff(c_339, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_334])).
% 2.77/1.45  tff(c_340, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_332])).
% 2.77/1.45  tff(c_132, plain, (![B_61, A_62]: (r1_tarski(k2_relat_1(B_61), A_62) | ~v5_relat_1(B_61, A_62) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.77/1.45  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.77/1.45  tff(c_72, plain, (![B_43, A_44]: (B_43=A_44 | ~r1_tarski(B_43, A_44) | ~r1_tarski(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.77/1.45  tff(c_81, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_72])).
% 2.77/1.45  tff(c_143, plain, (![B_61]: (k2_relat_1(B_61)=k1_xboole_0 | ~v5_relat_1(B_61, k1_xboole_0) | ~v1_relat_1(B_61))), inference(resolution, [status(thm)], [c_132, c_81])).
% 2.77/1.45  tff(c_416, plain, (![B_125]: (k2_relat_1(B_125)='#skF_3' | ~v5_relat_1(B_125, '#skF_3') | ~v1_relat_1(B_125))), inference(demodulation, [status(thm), theory('equality')], [c_340, c_340, c_143])).
% 2.77/1.45  tff(c_419, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_150, c_416])).
% 2.77/1.45  tff(c_422, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_419])).
% 2.77/1.45  tff(c_424, plain, $false, inference(negUnitSimplification, [status(thm)], [c_186, c_422])).
% 2.77/1.45  tff(c_435, plain, (![D_126]: (r2_hidden(D_126, k2_relat_1('#skF_4')) | ~r2_hidden(D_126, '#skF_3'))), inference(splitRight, [status(thm)], [c_223])).
% 2.77/1.45  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.77/1.45  tff(c_450, plain, (![A_131]: (r1_tarski(A_131, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_1'(A_131, k2_relat_1('#skF_4')), '#skF_3'))), inference(resolution, [status(thm)], [c_435, c_4])).
% 2.77/1.45  tff(c_460, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_450])).
% 2.77/1.45  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.77/1.45  tff(c_144, plain, (![B_61, A_62]: (k2_relat_1(B_61)=A_62 | ~r1_tarski(A_62, k2_relat_1(B_61)) | ~v5_relat_1(B_61, A_62) | ~v1_relat_1(B_61))), inference(resolution, [status(thm)], [c_132, c_8])).
% 2.77/1.45  tff(c_463, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_460, c_144])).
% 2.77/1.45  tff(c_470, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_150, c_463])).
% 2.77/1.45  tff(c_472, plain, $false, inference(negUnitSimplification, [status(thm)], [c_186, c_470])).
% 2.77/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.45  
% 2.77/1.45  Inference rules
% 2.77/1.45  ----------------------
% 2.77/1.45  #Ref     : 0
% 2.77/1.45  #Sup     : 80
% 2.77/1.45  #Fact    : 0
% 2.77/1.45  #Define  : 0
% 2.77/1.45  #Split   : 5
% 2.77/1.45  #Chain   : 0
% 2.77/1.45  #Close   : 0
% 2.77/1.45  
% 2.77/1.45  Ordering : KBO
% 2.77/1.45  
% 2.77/1.45  Simplification rules
% 2.77/1.45  ----------------------
% 2.77/1.45  #Subsume      : 12
% 2.77/1.45  #Demod        : 55
% 2.77/1.45  #Tautology    : 25
% 2.77/1.45  #SimpNegUnit  : 2
% 2.77/1.45  #BackRed      : 19
% 2.77/1.45  
% 2.77/1.45  #Partial instantiations: 0
% 2.77/1.45  #Strategies tried      : 1
% 2.77/1.45  
% 2.77/1.45  Timing (in seconds)
% 2.77/1.45  ----------------------
% 2.77/1.45  Preprocessing        : 0.35
% 2.77/1.45  Parsing              : 0.19
% 2.77/1.45  CNF conversion       : 0.02
% 2.77/1.45  Main loop            : 0.30
% 2.77/1.45  Inferencing          : 0.11
% 2.77/1.45  Reduction            : 0.08
% 2.77/1.45  Demodulation         : 0.06
% 2.77/1.45  BG Simplification    : 0.02
% 2.77/1.45  Subsumption          : 0.07
% 2.77/1.45  Abstraction          : 0.02
% 2.77/1.45  MUC search           : 0.00
% 2.77/1.45  Cooper               : 0.00
% 2.77/1.45  Total                : 0.68
% 2.77/1.45  Index Insertion      : 0.00
% 2.77/1.45  Index Deletion       : 0.00
% 2.77/1.45  Index Matching       : 0.00
% 2.77/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
