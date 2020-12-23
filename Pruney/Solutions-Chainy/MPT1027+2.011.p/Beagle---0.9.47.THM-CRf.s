%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:43 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   67 (  94 expanded)
%              Number of leaves         :   34 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :  107 ( 203 expanded)
%              Number of equality atoms :   26 (  40 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_129,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_106,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_68,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_50,axiom,(
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

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_116,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_54,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_62,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54])).

tff(c_90,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_94,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_90])).

tff(c_97,plain,(
    ! [C_44,B_45,A_46] :
      ( v5_relat_1(C_44,B_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_46,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_101,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_97])).

tff(c_56,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_611,plain,(
    ! [B_141,C_142,A_143] :
      ( k1_xboole_0 = B_141
      | v1_funct_2(C_142,A_143,B_141)
      | k1_relset_1(A_143,B_141,C_142) != A_143
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_143,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_620,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_58,c_611])).

tff(c_627,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_620])).

tff(c_628,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_627])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_111,plain,(
    ! [A_52,B_53,C_54] :
      ( ~ r1_xboole_0(A_52,B_53)
      | ~ r2_hidden(C_54,B_53)
      | ~ r2_hidden(C_54,A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_115,plain,(
    ! [C_55] : ~ r2_hidden(C_55,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_111])).

tff(c_130,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_115])).

tff(c_695,plain,(
    ! [B_145] : r1_tarski('#skF_4',B_145) ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_130])).

tff(c_102,plain,(
    ! [B_47,A_48] :
      ( r1_tarski(k2_relat_1(B_47),A_48)
      | ~ v5_relat_1(B_47,A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_105,plain,(
    ! [B_47,A_48] :
      ( k2_relat_1(B_47) = A_48
      | ~ r1_tarski(A_48,k2_relat_1(B_47))
      | ~ v5_relat_1(B_47,A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_102,c_14])).

tff(c_780,plain,(
    ! [B_157] :
      ( k2_relat_1(B_157) = '#skF_4'
      | ~ v5_relat_1(B_157,'#skF_4')
      | ~ v1_relat_1(B_157) ) ),
    inference(resolution,[status(thm)],[c_695,c_105])).

tff(c_783,plain,
    ( k2_relat_1('#skF_5') = '#skF_4'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_101,c_780])).

tff(c_786,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_783])).

tff(c_291,plain,(
    ! [A_89,B_90,C_91] :
      ( k1_relset_1(A_89,B_90,C_91) = k1_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_294,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_291])).

tff(c_296,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_294])).

tff(c_50,plain,(
    ! [A_28] :
      ( v1_funct_2(A_28,k1_relat_1(A_28),k2_relat_1(A_28))
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_300,plain,
    ( v1_funct_2('#skF_5','#skF_3',k2_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_50])).

tff(c_304,plain,(
    v1_funct_2('#skF_5','#skF_3',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_60,c_300])).

tff(c_790,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_304])).

tff(c_795,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_790])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:06:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.54  
% 2.85/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.54  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.85/1.54  
% 2.85/1.54  %Foreground sorts:
% 2.85/1.54  
% 2.85/1.54  
% 2.85/1.54  %Background operators:
% 2.85/1.54  
% 2.85/1.54  
% 2.85/1.54  %Foreground operators:
% 2.85/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.85/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.85/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.85/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.85/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.85/1.54  tff('#skF_5', type, '#skF_5': $i).
% 2.85/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.85/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.85/1.54  tff('#skF_3', type, '#skF_3': $i).
% 2.85/1.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.85/1.54  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.85/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.85/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.85/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.85/1.54  tff('#skF_4', type, '#skF_4': $i).
% 2.85/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.85/1.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.85/1.54  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.85/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.85/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.85/1.54  
% 2.85/1.56  tff(f_129, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_funct_2)).
% 2.85/1.56  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.85/1.56  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.85/1.56  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.85/1.56  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.85/1.56  tff(f_68, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.85/1.56  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.85/1.56  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.85/1.56  tff(f_56, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.85/1.56  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.85/1.56  tff(f_116, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 2.85/1.56  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.85/1.56  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.85/1.56  tff(c_54, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.85/1.56  tff(c_62, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54])).
% 2.85/1.56  tff(c_90, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.85/1.56  tff(c_94, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_90])).
% 2.85/1.56  tff(c_97, plain, (![C_44, B_45, A_46]: (v5_relat_1(C_44, B_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_46, B_45))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.85/1.56  tff(c_101, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_97])).
% 2.85/1.56  tff(c_56, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.85/1.56  tff(c_611, plain, (![B_141, C_142, A_143]: (k1_xboole_0=B_141 | v1_funct_2(C_142, A_143, B_141) | k1_relset_1(A_143, B_141, C_142)!=A_143 | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_143, B_141))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.85/1.56  tff(c_620, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_3'), inference(resolution, [status(thm)], [c_58, c_611])).
% 2.85/1.56  tff(c_627, plain, (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_620])).
% 2.85/1.56  tff(c_628, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_62, c_627])).
% 2.85/1.56  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.85/1.56  tff(c_20, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.85/1.56  tff(c_111, plain, (![A_52, B_53, C_54]: (~r1_xboole_0(A_52, B_53) | ~r2_hidden(C_54, B_53) | ~r2_hidden(C_54, A_52))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.85/1.56  tff(c_115, plain, (![C_55]: (~r2_hidden(C_55, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_111])).
% 2.85/1.56  tff(c_130, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_115])).
% 2.85/1.56  tff(c_695, plain, (![B_145]: (r1_tarski('#skF_4', B_145))), inference(demodulation, [status(thm), theory('equality')], [c_628, c_130])).
% 2.85/1.56  tff(c_102, plain, (![B_47, A_48]: (r1_tarski(k2_relat_1(B_47), A_48) | ~v5_relat_1(B_47, A_48) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.85/1.56  tff(c_14, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.85/1.56  tff(c_105, plain, (![B_47, A_48]: (k2_relat_1(B_47)=A_48 | ~r1_tarski(A_48, k2_relat_1(B_47)) | ~v5_relat_1(B_47, A_48) | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_102, c_14])).
% 2.85/1.56  tff(c_780, plain, (![B_157]: (k2_relat_1(B_157)='#skF_4' | ~v5_relat_1(B_157, '#skF_4') | ~v1_relat_1(B_157))), inference(resolution, [status(thm)], [c_695, c_105])).
% 2.85/1.56  tff(c_783, plain, (k2_relat_1('#skF_5')='#skF_4' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_101, c_780])).
% 2.85/1.56  tff(c_786, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_783])).
% 2.85/1.56  tff(c_291, plain, (![A_89, B_90, C_91]: (k1_relset_1(A_89, B_90, C_91)=k1_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.85/1.56  tff(c_294, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_291])).
% 2.85/1.56  tff(c_296, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_294])).
% 2.85/1.56  tff(c_50, plain, (![A_28]: (v1_funct_2(A_28, k1_relat_1(A_28), k2_relat_1(A_28)) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.85/1.56  tff(c_300, plain, (v1_funct_2('#skF_5', '#skF_3', k2_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_296, c_50])).
% 2.85/1.56  tff(c_304, plain, (v1_funct_2('#skF_5', '#skF_3', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_60, c_300])).
% 2.85/1.56  tff(c_790, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_786, c_304])).
% 2.85/1.56  tff(c_795, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_790])).
% 2.85/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.56  
% 2.85/1.56  Inference rules
% 2.85/1.56  ----------------------
% 2.85/1.56  #Ref     : 0
% 2.85/1.56  #Sup     : 148
% 2.85/1.56  #Fact    : 0
% 2.85/1.56  #Define  : 0
% 2.85/1.56  #Split   : 0
% 2.85/1.56  #Chain   : 0
% 2.85/1.56  #Close   : 0
% 2.85/1.56  
% 2.85/1.56  Ordering : KBO
% 2.85/1.56  
% 2.85/1.56  Simplification rules
% 2.85/1.56  ----------------------
% 2.85/1.56  #Subsume      : 39
% 2.85/1.56  #Demod        : 91
% 2.85/1.56  #Tautology    : 48
% 2.85/1.56  #SimpNegUnit  : 2
% 2.85/1.56  #BackRed      : 35
% 2.85/1.56  
% 2.85/1.56  #Partial instantiations: 0
% 2.85/1.56  #Strategies tried      : 1
% 2.85/1.56  
% 2.85/1.56  Timing (in seconds)
% 2.85/1.56  ----------------------
% 3.07/1.56  Preprocessing        : 0.36
% 3.07/1.56  Parsing              : 0.19
% 3.07/1.56  CNF conversion       : 0.02
% 3.07/1.56  Main loop            : 0.33
% 3.07/1.56  Inferencing          : 0.12
% 3.07/1.56  Reduction            : 0.10
% 3.07/1.56  Demodulation         : 0.07
% 3.07/1.56  BG Simplification    : 0.02
% 3.07/1.56  Subsumption          : 0.07
% 3.07/1.56  Abstraction          : 0.02
% 3.07/1.56  MUC search           : 0.00
% 3.07/1.56  Cooper               : 0.00
% 3.07/1.56  Total                : 0.72
% 3.07/1.56  Index Insertion      : 0.00
% 3.07/1.56  Index Deletion       : 0.00
% 3.07/1.56  Index Matching       : 0.00
% 3.07/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
