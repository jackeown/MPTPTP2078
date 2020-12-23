%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:56 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 105 expanded)
%              Number of leaves         :   35 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  104 ( 257 expanded)
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

tff(f_110,negated_conjecture,(
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

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_77,axiom,(
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

tff(f_47,axiom,(
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

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_52,plain,(
    m1_subset_1('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_58,plain,(
    ! [C_72,A_73,B_74] :
      ( v1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_62,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_46,c_58])).

tff(c_50,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_48,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_82,plain,(
    ! [A_78,B_79,C_80] :
      ( k1_relset_1(A_78,B_79,C_80) = k1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_86,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_46,c_82])).

tff(c_117,plain,(
    ! [B_99,A_100,C_101] :
      ( k1_xboole_0 = B_99
      | k1_relset_1(A_100,B_99,C_101) = A_100
      | ~ v1_funct_2(C_101,A_100,B_99)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_120,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_117])).

tff(c_123,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_86,c_120])).

tff(c_124,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_6,plain,(
    ! [A_3,D_42] :
      ( r2_hidden(k1_funct_1(A_3,D_42),k2_relat_1(A_3))
      | ~ r2_hidden(D_42,k1_relat_1(A_3))
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_174,plain,(
    ! [A_117,B_118,C_119,D_120] :
      ( k3_funct_2(A_117,B_118,C_119,D_120) = k1_funct_1(C_119,D_120)
      | ~ m1_subset_1(D_120,A_117)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118)))
      | ~ v1_funct_2(C_119,A_117,B_118)
      | ~ v1_funct_1(C_119)
      | v1_xboole_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_178,plain,(
    ! [B_118,C_119] :
      ( k3_funct_2('#skF_5',B_118,C_119,'#skF_7') = k1_funct_1(C_119,'#skF_7')
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_118)))
      | ~ v1_funct_2(C_119,'#skF_5',B_118)
      | ~ v1_funct_1(C_119)
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_52,c_174])).

tff(c_183,plain,(
    ! [B_121,C_122] :
      ( k3_funct_2('#skF_5',B_121,C_122,'#skF_7') = k1_funct_1(C_122,'#skF_7')
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_121)))
      | ~ v1_funct_2(C_122,'#skF_5',B_121)
      | ~ v1_funct_1(C_122) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_178])).

tff(c_186,plain,
    ( k3_funct_2('#skF_5','#skF_6','#skF_8','#skF_7') = k1_funct_1('#skF_8','#skF_7')
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_46,c_183])).

tff(c_189,plain,(
    k3_funct_2('#skF_5','#skF_6','#skF_8','#skF_7') = k1_funct_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_186])).

tff(c_67,plain,(
    ! [A_75,B_76,C_77] :
      ( k2_relset_1(A_75,B_76,C_77) = k2_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_71,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_46,c_67])).

tff(c_44,plain,(
    ~ r2_hidden(k3_funct_2('#skF_5','#skF_6','#skF_8','#skF_7'),k2_relset_1('#skF_5','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_72,plain,(
    ~ r2_hidden(k3_funct_2('#skF_5','#skF_6','#skF_8','#skF_7'),k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_44])).

tff(c_191,plain,(
    ~ r2_hidden(k1_funct_1('#skF_8','#skF_7'),k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_72])).

tff(c_198,plain,
    ( ~ r2_hidden('#skF_7',k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_6,c_191])).

tff(c_204,plain,(
    ~ r2_hidden('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_50,c_124,c_198])).

tff(c_208,plain,
    ( v1_xboole_0('#skF_5')
    | ~ m1_subset_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_204])).

tff(c_211,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_208])).

tff(c_213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_211])).

tff(c_214,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_222,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_2])).

tff(c_224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:10:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.29  
% 2.26/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.29  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 2.26/1.29  
% 2.26/1.29  %Foreground sorts:
% 2.26/1.29  
% 2.26/1.29  
% 2.26/1.29  %Background operators:
% 2.26/1.29  
% 2.26/1.29  
% 2.26/1.29  %Foreground operators:
% 2.26/1.29  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.26/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.26/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.29  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.26/1.29  tff('#skF_7', type, '#skF_7': $i).
% 2.26/1.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.26/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.26/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.26/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.26/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.26/1.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.26/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.26/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.26/1.29  tff('#skF_8', type, '#skF_8': $i).
% 2.26/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.26/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.26/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.26/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.26/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.26/1.29  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.26/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.26/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.26/1.29  
% 2.26/1.31  tff(f_110, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, A) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_hidden(k3_funct_2(A, B, D, C), k2_relset_1(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_funct_2)).
% 2.26/1.31  tff(f_32, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.26/1.31  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.26/1.31  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.26/1.31  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.26/1.31  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 2.26/1.31  tff(f_90, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.26/1.31  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.26/1.31  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.26/1.31  tff(c_54, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.26/1.31  tff(c_56, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.26/1.31  tff(c_52, plain, (m1_subset_1('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.26/1.31  tff(c_4, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.26/1.31  tff(c_46, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.26/1.31  tff(c_58, plain, (![C_72, A_73, B_74]: (v1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.26/1.31  tff(c_62, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_46, c_58])).
% 2.26/1.31  tff(c_50, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.26/1.31  tff(c_48, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.26/1.31  tff(c_82, plain, (![A_78, B_79, C_80]: (k1_relset_1(A_78, B_79, C_80)=k1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.26/1.31  tff(c_86, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_46, c_82])).
% 2.26/1.31  tff(c_117, plain, (![B_99, A_100, C_101]: (k1_xboole_0=B_99 | k1_relset_1(A_100, B_99, C_101)=A_100 | ~v1_funct_2(C_101, A_100, B_99) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.26/1.31  tff(c_120, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_46, c_117])).
% 2.26/1.31  tff(c_123, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_86, c_120])).
% 2.26/1.31  tff(c_124, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_123])).
% 2.26/1.31  tff(c_6, plain, (![A_3, D_42]: (r2_hidden(k1_funct_1(A_3, D_42), k2_relat_1(A_3)) | ~r2_hidden(D_42, k1_relat_1(A_3)) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.26/1.31  tff(c_174, plain, (![A_117, B_118, C_119, D_120]: (k3_funct_2(A_117, B_118, C_119, D_120)=k1_funct_1(C_119, D_120) | ~m1_subset_1(D_120, A_117) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))) | ~v1_funct_2(C_119, A_117, B_118) | ~v1_funct_1(C_119) | v1_xboole_0(A_117))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.26/1.31  tff(c_178, plain, (![B_118, C_119]: (k3_funct_2('#skF_5', B_118, C_119, '#skF_7')=k1_funct_1(C_119, '#skF_7') | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_118))) | ~v1_funct_2(C_119, '#skF_5', B_118) | ~v1_funct_1(C_119) | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_52, c_174])).
% 2.26/1.31  tff(c_183, plain, (![B_121, C_122]: (k3_funct_2('#skF_5', B_121, C_122, '#skF_7')=k1_funct_1(C_122, '#skF_7') | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_121))) | ~v1_funct_2(C_122, '#skF_5', B_121) | ~v1_funct_1(C_122))), inference(negUnitSimplification, [status(thm)], [c_56, c_178])).
% 2.26/1.31  tff(c_186, plain, (k3_funct_2('#skF_5', '#skF_6', '#skF_8', '#skF_7')=k1_funct_1('#skF_8', '#skF_7') | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6') | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_46, c_183])).
% 2.26/1.31  tff(c_189, plain, (k3_funct_2('#skF_5', '#skF_6', '#skF_8', '#skF_7')=k1_funct_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_186])).
% 2.26/1.31  tff(c_67, plain, (![A_75, B_76, C_77]: (k2_relset_1(A_75, B_76, C_77)=k2_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.26/1.31  tff(c_71, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_46, c_67])).
% 2.26/1.31  tff(c_44, plain, (~r2_hidden(k3_funct_2('#skF_5', '#skF_6', '#skF_8', '#skF_7'), k2_relset_1('#skF_5', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.26/1.31  tff(c_72, plain, (~r2_hidden(k3_funct_2('#skF_5', '#skF_6', '#skF_8', '#skF_7'), k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_44])).
% 2.26/1.31  tff(c_191, plain, (~r2_hidden(k1_funct_1('#skF_8', '#skF_7'), k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_72])).
% 2.26/1.31  tff(c_198, plain, (~r2_hidden('#skF_7', k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_6, c_191])).
% 2.26/1.31  tff(c_204, plain, (~r2_hidden('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_50, c_124, c_198])).
% 2.26/1.31  tff(c_208, plain, (v1_xboole_0('#skF_5') | ~m1_subset_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_4, c_204])).
% 2.26/1.31  tff(c_211, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_208])).
% 2.26/1.31  tff(c_213, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_211])).
% 2.26/1.31  tff(c_214, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_123])).
% 2.26/1.31  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.26/1.31  tff(c_222, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_214, c_2])).
% 2.26/1.31  tff(c_224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_222])).
% 2.26/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.31  
% 2.26/1.31  Inference rules
% 2.26/1.31  ----------------------
% 2.26/1.31  #Ref     : 0
% 2.26/1.31  #Sup     : 36
% 2.26/1.31  #Fact    : 0
% 2.26/1.31  #Define  : 0
% 2.26/1.31  #Split   : 2
% 2.26/1.31  #Chain   : 0
% 2.26/1.31  #Close   : 0
% 2.26/1.31  
% 2.26/1.31  Ordering : KBO
% 2.26/1.31  
% 2.26/1.31  Simplification rules
% 2.26/1.31  ----------------------
% 2.26/1.31  #Subsume      : 1
% 2.26/1.31  #Demod        : 40
% 2.26/1.31  #Tautology    : 16
% 2.26/1.31  #SimpNegUnit  : 3
% 2.26/1.31  #BackRed      : 11
% 2.26/1.31  
% 2.26/1.31  #Partial instantiations: 0
% 2.26/1.31  #Strategies tried      : 1
% 2.26/1.31  
% 2.26/1.31  Timing (in seconds)
% 2.26/1.31  ----------------------
% 2.26/1.31  Preprocessing        : 0.34
% 2.26/1.31  Parsing              : 0.17
% 2.26/1.31  CNF conversion       : 0.03
% 2.26/1.31  Main loop            : 0.21
% 2.26/1.31  Inferencing          : 0.08
% 2.26/1.31  Reduction            : 0.06
% 2.60/1.31  Demodulation         : 0.04
% 2.60/1.31  BG Simplification    : 0.02
% 2.60/1.31  Subsumption          : 0.04
% 2.60/1.31  Abstraction          : 0.01
% 2.60/1.31  MUC search           : 0.00
% 2.60/1.31  Cooper               : 0.00
% 2.60/1.31  Total                : 0.58
% 2.60/1.31  Index Insertion      : 0.00
% 2.60/1.31  Index Deletion       : 0.00
% 2.60/1.31  Index Matching       : 0.00
% 2.60/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
