%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:56 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 108 expanded)
%              Number of leaves         :   36 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  110 ( 263 expanded)
%              Number of equality atoms :   28 (  43 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

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
                ( m1_subset_1(C,A)
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,A,B)
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
                   => r2_hidden(k3_funct_2(A,B,D,C),k2_relset_1(A,B,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_41,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_82,axiom,(
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

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_54,plain,(
    m1_subset_1('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_48,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_65,plain,(
    ! [B_76,A_77] :
      ( v1_relat_1(B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_77))
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_68,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_48,c_65])).

tff(c_71,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_68])).

tff(c_52,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_50,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_88,plain,(
    ! [A_82,B_83,C_84] :
      ( k1_relset_1(A_82,B_83,C_84) = k1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_92,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_88])).

tff(c_121,plain,(
    ! [B_100,A_101,C_102] :
      ( k1_xboole_0 = B_100
      | k1_relset_1(A_101,B_100,C_102) = A_101
      | ~ v1_funct_2(C_102,A_101,B_100)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_101,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_124,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_121])).

tff(c_127,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_92,c_124])).

tff(c_128,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_10,plain,(
    ! [A_8,D_47] :
      ( r2_hidden(k1_funct_1(A_8,D_47),k2_relat_1(A_8))
      | ~ r2_hidden(D_47,k1_relat_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_184,plain,(
    ! [A_123,B_124,C_125,D_126] :
      ( k3_funct_2(A_123,B_124,C_125,D_126) = k1_funct_1(C_125,D_126)
      | ~ m1_subset_1(D_126,A_123)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124)))
      | ~ v1_funct_2(C_125,A_123,B_124)
      | ~ v1_funct_1(C_125)
      | v1_xboole_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_188,plain,(
    ! [B_124,C_125] :
      ( k3_funct_2('#skF_5',B_124,C_125,'#skF_7') = k1_funct_1(C_125,'#skF_7')
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_124)))
      | ~ v1_funct_2(C_125,'#skF_5',B_124)
      | ~ v1_funct_1(C_125)
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_184])).

tff(c_193,plain,(
    ! [B_127,C_128] :
      ( k3_funct_2('#skF_5',B_127,C_128,'#skF_7') = k1_funct_1(C_128,'#skF_7')
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_127)))
      | ~ v1_funct_2(C_128,'#skF_5',B_127)
      | ~ v1_funct_1(C_128) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_188])).

tff(c_196,plain,
    ( k3_funct_2('#skF_5','#skF_6','#skF_8','#skF_7') = k1_funct_1('#skF_8','#skF_7')
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_193])).

tff(c_199,plain,(
    k3_funct_2('#skF_5','#skF_6','#skF_8','#skF_7') = k1_funct_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_196])).

tff(c_72,plain,(
    ! [A_78,B_79,C_80] :
      ( k2_relset_1(A_78,B_79,C_80) = k2_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_76,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_72])).

tff(c_46,plain,(
    ~ r2_hidden(k3_funct_2('#skF_5','#skF_6','#skF_8','#skF_7'),k2_relset_1('#skF_5','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_77,plain,(
    ~ r2_hidden(k3_funct_2('#skF_5','#skF_6','#skF_8','#skF_7'),k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_46])).

tff(c_201,plain,(
    ~ r2_hidden(k1_funct_1('#skF_8','#skF_7'),k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_77])).

tff(c_208,plain,
    ( ~ r2_hidden('#skF_7',k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_10,c_201])).

tff(c_214,plain,(
    ~ r2_hidden('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_52,c_128,c_208])).

tff(c_230,plain,
    ( v1_xboole_0('#skF_5')
    | ~ m1_subset_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_214])).

tff(c_233,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_230])).

tff(c_235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_233])).

tff(c_236,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_244,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_2])).

tff(c_246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_244])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:25:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.37  
% 2.43/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.37  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 2.43/1.37  
% 2.43/1.37  %Foreground sorts:
% 2.43/1.37  
% 2.43/1.37  
% 2.43/1.37  %Background operators:
% 2.43/1.37  
% 2.43/1.37  
% 2.43/1.37  %Foreground operators:
% 2.43/1.37  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.43/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.43/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.43/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.43/1.37  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.43/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.43/1.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.43/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.43/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.43/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.43/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.43/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.43/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.43/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.43/1.37  tff('#skF_8', type, '#skF_8': $i).
% 2.43/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.43/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.43/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.43/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.43/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.43/1.37  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.43/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.43/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.43/1.37  
% 2.73/1.38  tff(f_115, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_hidden(k3_funct_2(A, B, D, C), k2_relset_1(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_funct_2)).
% 2.73/1.38  tff(f_32, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.73/1.38  tff(f_41, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.73/1.38  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.73/1.38  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.73/1.38  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.73/1.38  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 2.73/1.38  tff(f_95, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.73/1.38  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.73/1.38  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.73/1.38  tff(c_56, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.73/1.38  tff(c_58, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.73/1.38  tff(c_54, plain, (m1_subset_1('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.73/1.38  tff(c_4, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.73/1.38  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.73/1.38  tff(c_48, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.73/1.38  tff(c_65, plain, (![B_76, A_77]: (v1_relat_1(B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_77)) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.73/1.38  tff(c_68, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_48, c_65])).
% 2.73/1.38  tff(c_71, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_68])).
% 2.73/1.38  tff(c_52, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.73/1.38  tff(c_50, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.73/1.38  tff(c_88, plain, (![A_82, B_83, C_84]: (k1_relset_1(A_82, B_83, C_84)=k1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.73/1.38  tff(c_92, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_48, c_88])).
% 2.73/1.38  tff(c_121, plain, (![B_100, A_101, C_102]: (k1_xboole_0=B_100 | k1_relset_1(A_101, B_100, C_102)=A_101 | ~v1_funct_2(C_102, A_101, B_100) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.73/1.38  tff(c_124, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_48, c_121])).
% 2.73/1.38  tff(c_127, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_92, c_124])).
% 2.73/1.38  tff(c_128, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_127])).
% 2.73/1.38  tff(c_10, plain, (![A_8, D_47]: (r2_hidden(k1_funct_1(A_8, D_47), k2_relat_1(A_8)) | ~r2_hidden(D_47, k1_relat_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.73/1.38  tff(c_184, plain, (![A_123, B_124, C_125, D_126]: (k3_funct_2(A_123, B_124, C_125, D_126)=k1_funct_1(C_125, D_126) | ~m1_subset_1(D_126, A_123) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))) | ~v1_funct_2(C_125, A_123, B_124) | ~v1_funct_1(C_125) | v1_xboole_0(A_123))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.73/1.38  tff(c_188, plain, (![B_124, C_125]: (k3_funct_2('#skF_5', B_124, C_125, '#skF_7')=k1_funct_1(C_125, '#skF_7') | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_124))) | ~v1_funct_2(C_125, '#skF_5', B_124) | ~v1_funct_1(C_125) | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_184])).
% 2.73/1.38  tff(c_193, plain, (![B_127, C_128]: (k3_funct_2('#skF_5', B_127, C_128, '#skF_7')=k1_funct_1(C_128, '#skF_7') | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_127))) | ~v1_funct_2(C_128, '#skF_5', B_127) | ~v1_funct_1(C_128))), inference(negUnitSimplification, [status(thm)], [c_58, c_188])).
% 2.73/1.38  tff(c_196, plain, (k3_funct_2('#skF_5', '#skF_6', '#skF_8', '#skF_7')=k1_funct_1('#skF_8', '#skF_7') | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6') | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_48, c_193])).
% 2.73/1.38  tff(c_199, plain, (k3_funct_2('#skF_5', '#skF_6', '#skF_8', '#skF_7')=k1_funct_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_196])).
% 2.73/1.38  tff(c_72, plain, (![A_78, B_79, C_80]: (k2_relset_1(A_78, B_79, C_80)=k2_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.73/1.38  tff(c_76, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_48, c_72])).
% 2.73/1.38  tff(c_46, plain, (~r2_hidden(k3_funct_2('#skF_5', '#skF_6', '#skF_8', '#skF_7'), k2_relset_1('#skF_5', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.73/1.38  tff(c_77, plain, (~r2_hidden(k3_funct_2('#skF_5', '#skF_6', '#skF_8', '#skF_7'), k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_46])).
% 2.73/1.38  tff(c_201, plain, (~r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_77])).
% 2.73/1.38  tff(c_208, plain, (~r2_hidden('#skF_7', k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_10, c_201])).
% 2.73/1.38  tff(c_214, plain, (~r2_hidden('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_52, c_128, c_208])).
% 2.73/1.38  tff(c_230, plain, (v1_xboole_0('#skF_5') | ~m1_subset_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_4, c_214])).
% 2.73/1.38  tff(c_233, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_230])).
% 2.73/1.38  tff(c_235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_233])).
% 2.73/1.38  tff(c_236, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_127])).
% 2.73/1.38  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.73/1.38  tff(c_244, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_236, c_2])).
% 2.73/1.38  tff(c_246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_244])).
% 2.73/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.38  
% 2.73/1.38  Inference rules
% 2.73/1.38  ----------------------
% 2.73/1.38  #Ref     : 0
% 2.73/1.38  #Sup     : 41
% 2.73/1.38  #Fact    : 0
% 2.73/1.38  #Define  : 0
% 2.73/1.38  #Split   : 2
% 2.73/1.38  #Chain   : 0
% 2.73/1.38  #Close   : 0
% 2.73/1.38  
% 2.73/1.38  Ordering : KBO
% 2.73/1.39  
% 2.73/1.39  Simplification rules
% 2.73/1.39  ----------------------
% 2.73/1.39  #Subsume      : 1
% 2.73/1.39  #Demod        : 45
% 2.73/1.39  #Tautology    : 16
% 2.73/1.39  #SimpNegUnit  : 3
% 2.73/1.39  #BackRed      : 11
% 2.73/1.39  
% 2.73/1.39  #Partial instantiations: 0
% 2.73/1.39  #Strategies tried      : 1
% 2.73/1.39  
% 2.73/1.39  Timing (in seconds)
% 2.73/1.39  ----------------------
% 2.73/1.39  Preprocessing        : 0.35
% 2.73/1.39  Parsing              : 0.17
% 2.73/1.39  CNF conversion       : 0.03
% 2.73/1.39  Main loop            : 0.26
% 2.73/1.39  Inferencing          : 0.09
% 2.73/1.39  Reduction            : 0.08
% 2.73/1.39  Demodulation         : 0.06
% 2.73/1.39  BG Simplification    : 0.02
% 2.73/1.39  Subsumption          : 0.05
% 2.73/1.39  Abstraction          : 0.02
% 2.73/1.39  MUC search           : 0.00
% 2.73/1.39  Cooper               : 0.00
% 2.73/1.39  Total                : 0.65
% 2.73/1.39  Index Insertion      : 0.00
% 2.73/1.39  Index Deletion       : 0.00
% 2.73/1.39  Index Matching       : 0.00
% 2.73/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
