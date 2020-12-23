%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:47 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 514 expanded)
%              Number of leaves         :   29 ( 187 expanded)
%              Depth                    :   12
%              Number of atoms          :  118 (1459 expanded)
%              Number of equality atoms :   42 ( 397 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_mcart_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_55,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_73,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_88,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
      & v1_relat_1(B)
      & v4_relat_1(B,A)
      & v5_relat_1(B,A)
      & v1_funct_1(B)
      & v1_funct_2(B,A,A)
      & v3_funct_2(B,A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_funct_2)).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_44,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_52,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44])).

tff(c_46,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_12,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_1'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_302,plain,(
    ! [B_75,C_76,A_77] :
      ( k1_xboole_0 = B_75
      | v1_funct_2(C_76,A_77,B_75)
      | k1_relset_1(A_77,B_75,C_76) != A_77
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_308,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_48,c_302])).

tff(c_319,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_308])).

tff(c_320,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_319])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_348,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_2])).

tff(c_6,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_347,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_320,c_6])).

tff(c_111,plain,(
    ! [C_37,B_38,A_39] :
      ( ~ v1_xboole_0(C_37)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(C_37))
      | ~ r2_hidden(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_122,plain,(
    ! [A_39] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_39,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_111])).

tff(c_123,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_403,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_123])).

tff(c_407,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_403])).

tff(c_410,plain,(
    ! [A_80] : ~ r2_hidden(A_80,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_415,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_12,c_410])).

tff(c_24,plain,(
    ! [B_21,C_22,A_20] :
      ( k1_xboole_0 = B_21
      | v1_funct_2(C_22,A_20,B_21)
      | k1_relset_1(A_20,B_21,C_22) != A_20
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_676,plain,(
    ! [B_120,C_121,A_122] :
      ( B_120 = '#skF_5'
      | v1_funct_2(C_121,A_122,B_120)
      | k1_relset_1(A_122,B_120,C_121) != A_122
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_122,B_120))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_24])).

tff(c_688,plain,
    ( '#skF_5' = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_48,c_676])).

tff(c_694,plain,
    ( '#skF_5' = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_688])).

tff(c_695,plain,(
    '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_694])).

tff(c_504,plain,(
    ! [A_93] :
      ( r2_hidden('#skF_1'(A_93),A_93)
      | A_93 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_12])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_90,plain,(
    ! [A_34] : m1_subset_1('#skF_2'(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_94,plain,(
    m1_subset_1('#skF_2'(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_90])).

tff(c_113,plain,(
    ! [A_39] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_39,'#skF_2'(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_94,c_111])).

tff(c_120,plain,(
    ! [A_39] : ~ r2_hidden(A_39,'#skF_2'(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_113])).

tff(c_426,plain,(
    ! [A_39] : ~ r2_hidden(A_39,'#skF_2'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_120])).

tff(c_516,plain,(
    '#skF_2'('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_504,c_426])).

tff(c_32,plain,(
    ! [A_23] : v1_funct_2('#skF_2'(A_23),A_23,A_23) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_533,plain,(
    v1_funct_2('#skF_5','#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_516,c_32])).

tff(c_707,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_695,c_695,c_533])).

tff(c_18,plain,(
    ! [A_20] :
      ( v1_funct_2(k1_xboole_0,A_20,k1_xboole_0)
      | k1_xboole_0 = A_20
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_20,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_56,plain,(
    ! [A_20] :
      ( v1_funct_2(k1_xboole_0,A_20,k1_xboole_0)
      | k1_xboole_0 = A_20
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_18])).

tff(c_458,plain,(
    ! [A_20] :
      ( v1_funct_2('#skF_5',A_20,'#skF_5')
      | A_20 = '#skF_5'
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_415,c_415,c_415,c_415,c_56])).

tff(c_459,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_458])).

tff(c_469,plain,(
    ! [A_88] :
      ( r2_hidden('#skF_1'(A_88),A_88)
      | A_88 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_12])).

tff(c_481,plain,(
    '#skF_2'('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_469,c_426])).

tff(c_416,plain,(
    m1_subset_1('#skF_2'('#skF_5'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_415,c_94])).

tff(c_484,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_416])).

tff(c_487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_459,c_484])).

tff(c_488,plain,(
    ! [A_20] :
      ( v1_funct_2('#skF_5',A_20,'#skF_5')
      | A_20 = '#skF_5' ) ),
    inference(splitRight,[status(thm)],[c_458])).

tff(c_823,plain,(
    ! [A_126] :
      ( v1_funct_2('#skF_4',A_126,'#skF_4')
      | A_126 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_695,c_695,c_488])).

tff(c_725,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_52])).

tff(c_827,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_823,c_725])).

tff(c_828,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_827,c_725])).

tff(c_832,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_707,c_828])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:03:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.44  
% 2.82/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.45  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_mcart_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.93/1.45  
% 2.93/1.45  %Foreground sorts:
% 2.93/1.45  
% 2.93/1.45  
% 2.93/1.45  %Background operators:
% 2.93/1.45  
% 2.93/1.45  
% 2.93/1.45  %Foreground operators:
% 2.93/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.93/1.45  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.93/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.93/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.93/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.93/1.45  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.93/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.93/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.93/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.93/1.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.93/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.93/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.93/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.93/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.93/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.93/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.93/1.45  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 2.93/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.93/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.93/1.45  
% 2.93/1.46  tff(f_101, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_funct_2)).
% 2.93/1.46  tff(f_55, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 2.93/1.46  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.93/1.46  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.93/1.46  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.93/1.46  tff(f_39, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.93/1.46  tff(f_88, axiom, (![A]: (?[B]: ((((((m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) & v1_relat_1(B)) & v4_relat_1(B, A)) & v5_relat_1(B, A)) & v1_funct_1(B)) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_funct_2)).
% 2.93/1.46  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.93/1.46  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.93/1.46  tff(c_44, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.93/1.46  tff(c_52, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44])).
% 2.93/1.46  tff(c_46, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.93/1.46  tff(c_12, plain, (![A_6]: (r2_hidden('#skF_1'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.93/1.46  tff(c_302, plain, (![B_75, C_76, A_77]: (k1_xboole_0=B_75 | v1_funct_2(C_76, A_77, B_75) | k1_relset_1(A_77, B_75, C_76)!=A_77 | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_75))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.93/1.46  tff(c_308, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_3'), inference(resolution, [status(thm)], [c_48, c_302])).
% 2.93/1.46  tff(c_319, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_308])).
% 2.93/1.46  tff(c_320, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_52, c_319])).
% 2.93/1.46  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.93/1.46  tff(c_348, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_320, c_2])).
% 2.93/1.46  tff(c_6, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.93/1.46  tff(c_347, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_320, c_320, c_6])).
% 2.93/1.46  tff(c_111, plain, (![C_37, B_38, A_39]: (~v1_xboole_0(C_37) | ~m1_subset_1(B_38, k1_zfmisc_1(C_37)) | ~r2_hidden(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.93/1.46  tff(c_122, plain, (![A_39]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_39, '#skF_5'))), inference(resolution, [status(thm)], [c_48, c_111])).
% 2.93/1.46  tff(c_123, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_122])).
% 2.93/1.46  tff(c_403, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_347, c_123])).
% 2.93/1.46  tff(c_407, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_348, c_403])).
% 2.93/1.46  tff(c_410, plain, (![A_80]: (~r2_hidden(A_80, '#skF_5'))), inference(splitRight, [status(thm)], [c_122])).
% 2.93/1.46  tff(c_415, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_12, c_410])).
% 2.93/1.46  tff(c_24, plain, (![B_21, C_22, A_20]: (k1_xboole_0=B_21 | v1_funct_2(C_22, A_20, B_21) | k1_relset_1(A_20, B_21, C_22)!=A_20 | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.93/1.46  tff(c_676, plain, (![B_120, C_121, A_122]: (B_120='#skF_5' | v1_funct_2(C_121, A_122, B_120) | k1_relset_1(A_122, B_120, C_121)!=A_122 | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_122, B_120))))), inference(demodulation, [status(thm), theory('equality')], [c_415, c_24])).
% 2.93/1.46  tff(c_688, plain, ('#skF_5'='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_3'), inference(resolution, [status(thm)], [c_48, c_676])).
% 2.93/1.46  tff(c_694, plain, ('#skF_5'='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_688])).
% 2.93/1.46  tff(c_695, plain, ('#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_52, c_694])).
% 2.93/1.46  tff(c_504, plain, (![A_93]: (r2_hidden('#skF_1'(A_93), A_93) | A_93='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_415, c_12])).
% 2.93/1.46  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.93/1.46  tff(c_90, plain, (![A_34]: (m1_subset_1('#skF_2'(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.93/1.46  tff(c_94, plain, (m1_subset_1('#skF_2'(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_90])).
% 2.93/1.46  tff(c_113, plain, (![A_39]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_39, '#skF_2'(k1_xboole_0)))), inference(resolution, [status(thm)], [c_94, c_111])).
% 2.93/1.46  tff(c_120, plain, (![A_39]: (~r2_hidden(A_39, '#skF_2'(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_113])).
% 2.93/1.46  tff(c_426, plain, (![A_39]: (~r2_hidden(A_39, '#skF_2'('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_415, c_120])).
% 2.93/1.46  tff(c_516, plain, ('#skF_2'('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_504, c_426])).
% 2.93/1.46  tff(c_32, plain, (![A_23]: (v1_funct_2('#skF_2'(A_23), A_23, A_23))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.93/1.46  tff(c_533, plain, (v1_funct_2('#skF_5', '#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_516, c_32])).
% 2.93/1.46  tff(c_707, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_695, c_695, c_695, c_533])).
% 2.93/1.46  tff(c_18, plain, (![A_20]: (v1_funct_2(k1_xboole_0, A_20, k1_xboole_0) | k1_xboole_0=A_20 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_20, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.93/1.46  tff(c_56, plain, (![A_20]: (v1_funct_2(k1_xboole_0, A_20, k1_xboole_0) | k1_xboole_0=A_20 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_18])).
% 2.93/1.46  tff(c_458, plain, (![A_20]: (v1_funct_2('#skF_5', A_20, '#skF_5') | A_20='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_415, c_415, c_415, c_415, c_415, c_56])).
% 2.93/1.46  tff(c_459, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_458])).
% 2.93/1.46  tff(c_469, plain, (![A_88]: (r2_hidden('#skF_1'(A_88), A_88) | A_88='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_415, c_12])).
% 2.93/1.46  tff(c_481, plain, ('#skF_2'('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_469, c_426])).
% 2.93/1.46  tff(c_416, plain, (m1_subset_1('#skF_2'('#skF_5'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_415, c_415, c_94])).
% 2.93/1.46  tff(c_484, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_481, c_416])).
% 2.93/1.46  tff(c_487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_459, c_484])).
% 2.93/1.46  tff(c_488, plain, (![A_20]: (v1_funct_2('#skF_5', A_20, '#skF_5') | A_20='#skF_5')), inference(splitRight, [status(thm)], [c_458])).
% 2.93/1.46  tff(c_823, plain, (![A_126]: (v1_funct_2('#skF_4', A_126, '#skF_4') | A_126='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_695, c_695, c_695, c_488])).
% 2.93/1.46  tff(c_725, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_695, c_52])).
% 2.93/1.46  tff(c_827, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_823, c_725])).
% 2.93/1.46  tff(c_828, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_827, c_725])).
% 2.93/1.46  tff(c_832, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_707, c_828])).
% 2.93/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.46  
% 2.93/1.46  Inference rules
% 2.93/1.46  ----------------------
% 2.93/1.46  #Ref     : 0
% 2.93/1.46  #Sup     : 156
% 2.93/1.46  #Fact    : 0
% 2.93/1.46  #Define  : 0
% 2.93/1.46  #Split   : 3
% 2.93/1.46  #Chain   : 0
% 2.93/1.46  #Close   : 0
% 2.93/1.46  
% 2.93/1.46  Ordering : KBO
% 2.93/1.46  
% 2.93/1.46  Simplification rules
% 2.93/1.46  ----------------------
% 2.93/1.46  #Subsume      : 18
% 2.93/1.46  #Demod        : 259
% 2.93/1.46  #Tautology    : 104
% 2.93/1.46  #SimpNegUnit  : 4
% 2.93/1.46  #BackRed      : 75
% 2.93/1.46  
% 2.93/1.46  #Partial instantiations: 0
% 2.93/1.46  #Strategies tried      : 1
% 2.93/1.46  
% 2.93/1.46  Timing (in seconds)
% 2.93/1.46  ----------------------
% 2.93/1.46  Preprocessing        : 0.30
% 2.93/1.46  Parsing              : 0.17
% 2.93/1.46  CNF conversion       : 0.02
% 2.93/1.47  Main loop            : 0.33
% 2.93/1.47  Inferencing          : 0.12
% 2.93/1.47  Reduction            : 0.11
% 2.93/1.47  Demodulation         : 0.08
% 2.93/1.47  BG Simplification    : 0.02
% 2.93/1.47  Subsumption          : 0.05
% 2.93/1.47  Abstraction          : 0.01
% 2.93/1.47  MUC search           : 0.00
% 2.93/1.47  Cooper               : 0.00
% 2.93/1.47  Total                : 0.67
% 2.93/1.47  Index Insertion      : 0.00
% 2.93/1.47  Index Deletion       : 0.00
% 2.93/1.47  Index Matching       : 0.00
% 2.93/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
