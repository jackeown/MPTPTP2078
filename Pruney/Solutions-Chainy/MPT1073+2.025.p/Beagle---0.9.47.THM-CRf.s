%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:01 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   58 (  73 expanded)
%              Number of leaves         :   34 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   84 ( 142 expanded)
%              Number of equality atoms :   17 (  26 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_119,plain,(
    ! [A_86,B_87,C_88,D_89] :
      ( k7_relset_1(A_86,B_87,C_88,D_89) = k9_relat_1(C_88,D_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_126,plain,(
    ! [D_89] : k7_relset_1('#skF_6','#skF_7','#skF_8',D_89) = k9_relat_1('#skF_8',D_89) ),
    inference(resolution,[status(thm)],[c_50,c_119])).

tff(c_154,plain,(
    ! [A_98,B_99,C_100] :
      ( k7_relset_1(A_98,B_99,C_100,A_98) = k2_relset_1(A_98,B_99,C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_159,plain,(
    k7_relset_1('#skF_6','#skF_7','#skF_8','#skF_6') = k2_relset_1('#skF_6','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_50,c_154])).

tff(c_162,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k9_relat_1('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_159])).

tff(c_48,plain,(
    r2_hidden('#skF_5',k2_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_165,plain,(
    r2_hidden('#skF_5',k9_relat_1('#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_48])).

tff(c_68,plain,(
    ! [C_68,A_69,B_70] :
      ( v1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_77,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_50,c_68])).

tff(c_54,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_16,plain,(
    ! [A_8,B_31,D_46] :
      ( k1_funct_1(A_8,'#skF_4'(A_8,B_31,k9_relat_1(A_8,B_31),D_46)) = D_46
      | ~ r2_hidden(D_46,k9_relat_1(A_8,B_31))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_211,plain,(
    ! [A_110,B_111,D_112] :
      ( r2_hidden('#skF_4'(A_110,B_111,k9_relat_1(A_110,B_111),D_112),B_111)
      | ~ r2_hidden(D_112,k9_relat_1(A_110,B_111))
      | ~ v1_funct_1(A_110)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_101,plain,(
    ! [A_78,C_79,B_80] :
      ( m1_subset_1(A_78,C_79)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(C_79))
      | ~ r2_hidden(A_78,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_106,plain,(
    ! [A_78,B_4,A_3] :
      ( m1_subset_1(A_78,B_4)
      | ~ r2_hidden(A_78,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_101])).

tff(c_268,plain,(
    ! [A_136,B_137,D_138,B_139] :
      ( m1_subset_1('#skF_4'(A_136,B_137,k9_relat_1(A_136,B_137),D_138),B_139)
      | ~ r1_tarski(B_137,B_139)
      | ~ r2_hidden(D_138,k9_relat_1(A_136,B_137))
      | ~ v1_funct_1(A_136)
      | ~ v1_relat_1(A_136) ) ),
    inference(resolution,[status(thm)],[c_211,c_106])).

tff(c_46,plain,(
    ! [E_61] :
      ( k1_funct_1('#skF_8',E_61) != '#skF_5'
      | ~ m1_subset_1(E_61,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_359,plain,(
    ! [A_154,B_155,D_156] :
      ( k1_funct_1('#skF_8','#skF_4'(A_154,B_155,k9_relat_1(A_154,B_155),D_156)) != '#skF_5'
      | ~ r1_tarski(B_155,'#skF_6')
      | ~ r2_hidden(D_156,k9_relat_1(A_154,B_155))
      | ~ v1_funct_1(A_154)
      | ~ v1_relat_1(A_154) ) ),
    inference(resolution,[status(thm)],[c_268,c_46])).

tff(c_363,plain,(
    ! [D_46,B_31] :
      ( D_46 != '#skF_5'
      | ~ r1_tarski(B_31,'#skF_6')
      | ~ r2_hidden(D_46,k9_relat_1('#skF_8',B_31))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_46,k9_relat_1('#skF_8',B_31))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_359])).

tff(c_367,plain,(
    ! [D_157,B_158] :
      ( D_157 != '#skF_5'
      | ~ r1_tarski(B_158,'#skF_6')
      | ~ r2_hidden(D_157,k9_relat_1('#skF_8',B_158)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_54,c_77,c_54,c_363])).

tff(c_394,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_165,c_367])).

tff(c_406,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_394])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:43:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.34  
% 2.39/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.35  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 2.39/1.35  
% 2.39/1.35  %Foreground sorts:
% 2.39/1.35  
% 2.39/1.35  
% 2.39/1.35  %Background operators:
% 2.39/1.35  
% 2.39/1.35  
% 2.39/1.35  %Foreground operators:
% 2.39/1.35  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.39/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.39/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.39/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.39/1.35  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.39/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.39/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.39/1.35  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.39/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.39/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.39/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.39/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.39/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.39/1.35  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.39/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.39/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.39/1.35  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.39/1.35  tff('#skF_8', type, '#skF_8': $i).
% 2.39/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.39/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.39/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.39/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.39/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.39/1.35  
% 2.39/1.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.39/1.36  tff(f_88, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 2.39/1.36  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.39/1.36  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.39/1.36  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.39/1.36  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 2.39/1.36  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.39/1.36  tff(f_41, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.39/1.36  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.39/1.36  tff(c_50, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.39/1.36  tff(c_119, plain, (![A_86, B_87, C_88, D_89]: (k7_relset_1(A_86, B_87, C_88, D_89)=k9_relat_1(C_88, D_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.39/1.36  tff(c_126, plain, (![D_89]: (k7_relset_1('#skF_6', '#skF_7', '#skF_8', D_89)=k9_relat_1('#skF_8', D_89))), inference(resolution, [status(thm)], [c_50, c_119])).
% 2.39/1.36  tff(c_154, plain, (![A_98, B_99, C_100]: (k7_relset_1(A_98, B_99, C_100, A_98)=k2_relset_1(A_98, B_99, C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.39/1.36  tff(c_159, plain, (k7_relset_1('#skF_6', '#skF_7', '#skF_8', '#skF_6')=k2_relset_1('#skF_6', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_50, c_154])).
% 2.39/1.36  tff(c_162, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k9_relat_1('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_159])).
% 2.39/1.36  tff(c_48, plain, (r2_hidden('#skF_5', k2_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.39/1.36  tff(c_165, plain, (r2_hidden('#skF_5', k9_relat_1('#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_48])).
% 2.39/1.36  tff(c_68, plain, (![C_68, A_69, B_70]: (v1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.39/1.36  tff(c_77, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_50, c_68])).
% 2.39/1.36  tff(c_54, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.39/1.36  tff(c_16, plain, (![A_8, B_31, D_46]: (k1_funct_1(A_8, '#skF_4'(A_8, B_31, k9_relat_1(A_8, B_31), D_46))=D_46 | ~r2_hidden(D_46, k9_relat_1(A_8, B_31)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.39/1.36  tff(c_211, plain, (![A_110, B_111, D_112]: (r2_hidden('#skF_4'(A_110, B_111, k9_relat_1(A_110, B_111), D_112), B_111) | ~r2_hidden(D_112, k9_relat_1(A_110, B_111)) | ~v1_funct_1(A_110) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.39/1.36  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.39/1.36  tff(c_101, plain, (![A_78, C_79, B_80]: (m1_subset_1(A_78, C_79) | ~m1_subset_1(B_80, k1_zfmisc_1(C_79)) | ~r2_hidden(A_78, B_80))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.39/1.36  tff(c_106, plain, (![A_78, B_4, A_3]: (m1_subset_1(A_78, B_4) | ~r2_hidden(A_78, A_3) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_10, c_101])).
% 2.39/1.36  tff(c_268, plain, (![A_136, B_137, D_138, B_139]: (m1_subset_1('#skF_4'(A_136, B_137, k9_relat_1(A_136, B_137), D_138), B_139) | ~r1_tarski(B_137, B_139) | ~r2_hidden(D_138, k9_relat_1(A_136, B_137)) | ~v1_funct_1(A_136) | ~v1_relat_1(A_136))), inference(resolution, [status(thm)], [c_211, c_106])).
% 2.39/1.36  tff(c_46, plain, (![E_61]: (k1_funct_1('#skF_8', E_61)!='#skF_5' | ~m1_subset_1(E_61, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.39/1.36  tff(c_359, plain, (![A_154, B_155, D_156]: (k1_funct_1('#skF_8', '#skF_4'(A_154, B_155, k9_relat_1(A_154, B_155), D_156))!='#skF_5' | ~r1_tarski(B_155, '#skF_6') | ~r2_hidden(D_156, k9_relat_1(A_154, B_155)) | ~v1_funct_1(A_154) | ~v1_relat_1(A_154))), inference(resolution, [status(thm)], [c_268, c_46])).
% 2.39/1.36  tff(c_363, plain, (![D_46, B_31]: (D_46!='#skF_5' | ~r1_tarski(B_31, '#skF_6') | ~r2_hidden(D_46, k9_relat_1('#skF_8', B_31)) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_46, k9_relat_1('#skF_8', B_31)) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_359])).
% 2.39/1.36  tff(c_367, plain, (![D_157, B_158]: (D_157!='#skF_5' | ~r1_tarski(B_158, '#skF_6') | ~r2_hidden(D_157, k9_relat_1('#skF_8', B_158)))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_54, c_77, c_54, c_363])).
% 2.39/1.36  tff(c_394, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_165, c_367])).
% 2.39/1.36  tff(c_406, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_394])).
% 2.39/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.36  
% 2.39/1.36  Inference rules
% 2.39/1.36  ----------------------
% 2.39/1.36  #Ref     : 0
% 2.39/1.36  #Sup     : 77
% 2.39/1.36  #Fact    : 0
% 2.39/1.36  #Define  : 0
% 2.39/1.36  #Split   : 1
% 2.39/1.36  #Chain   : 0
% 2.39/1.36  #Close   : 0
% 2.39/1.36  
% 2.39/1.36  Ordering : KBO
% 2.39/1.36  
% 2.39/1.36  Simplification rules
% 2.39/1.36  ----------------------
% 2.39/1.36  #Subsume      : 1
% 2.39/1.36  #Demod        : 20
% 2.39/1.36  #Tautology    : 24
% 2.39/1.36  #SimpNegUnit  : 0
% 2.39/1.36  #BackRed      : 3
% 2.39/1.36  
% 2.39/1.36  #Partial instantiations: 0
% 2.39/1.36  #Strategies tried      : 1
% 2.39/1.36  
% 2.39/1.36  Timing (in seconds)
% 2.39/1.36  ----------------------
% 2.39/1.36  Preprocessing        : 0.32
% 2.39/1.36  Parsing              : 0.16
% 2.39/1.36  CNF conversion       : 0.03
% 2.39/1.36  Main loop            : 0.26
% 2.39/1.36  Inferencing          : 0.10
% 2.39/1.36  Reduction            : 0.07
% 2.39/1.36  Demodulation         : 0.05
% 2.39/1.36  BG Simplification    : 0.02
% 2.39/1.36  Subsumption          : 0.05
% 2.39/1.36  Abstraction          : 0.02
% 2.39/1.36  MUC search           : 0.00
% 2.39/1.36  Cooper               : 0.00
% 2.39/1.36  Total                : 0.60
% 2.39/1.36  Index Insertion      : 0.00
% 2.39/1.36  Index Deletion       : 0.00
% 2.39/1.36  Index Matching       : 0.00
% 2.39/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
