%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:03 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 199 expanded)
%              Number of leaves         :   33 (  82 expanded)
%              Depth                    :   10
%              Number of atoms          :   85 ( 375 expanded)
%              Number of equality atoms :   24 ( 109 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_xboole_0,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,A))) )
       => k8_relset_1(k1_xboole_0,A,C,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_32,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_1'(A_18),A_18)
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_16,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_41,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_36])).

tff(c_159,plain,(
    ! [C_60,B_61,A_62] :
      ( ~ v1_xboole_0(C_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(C_60))
      | ~ r2_hidden(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_161,plain,(
    ! [A_62] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_62,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_41,c_159])).

tff(c_165,plain,(
    ! [A_63] : ~ r2_hidden(A_63,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_161])).

tff(c_170,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_165])).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_182,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_10])).

tff(c_76,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_81,plain,(
    ! [C_48] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_76])).

tff(c_85,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_41,c_81])).

tff(c_128,plain,(
    ! [C_56,B_57,A_58] :
      ( ~ v1_xboole_0(C_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(C_56))
      | ~ r2_hidden(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_130,plain,(
    ! [A_58] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_58,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_41,c_128])).

tff(c_134,plain,(
    ! [A_59] : ~ r2_hidden(A_59,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_130])).

tff(c_139,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_134])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_120,plain,(
    ! [B_54,A_55] :
      ( r1_tarski(k10_relat_1(B_54,A_55),k1_relat_1(B_54))
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_125,plain,(
    ! [A_55] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_55),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_120])).

tff(c_127,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_140,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_127])).

tff(c_156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_140])).

tff(c_157,plain,(
    ! [A_55] : r1_tarski(k10_relat_1(k1_xboole_0,A_55),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_244,plain,(
    ! [A_71] : r1_tarski(k10_relat_1('#skF_4',A_71),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_170,c_157])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_246,plain,(
    ! [A_71] :
      ( k10_relat_1('#skF_4',A_71) = '#skF_4'
      | ~ r1_tarski('#skF_4',k10_relat_1('#skF_4',A_71)) ) ),
    inference(resolution,[status(thm)],[c_244,c_4])).

tff(c_249,plain,(
    ! [A_71] : k10_relat_1('#skF_4',A_71) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_246])).

tff(c_179,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_41])).

tff(c_219,plain,(
    ! [B_70] : k2_zfmisc_1('#skF_4',B_70) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_170,c_16])).

tff(c_28,plain,(
    ! [A_14,B_15,C_16,D_17] :
      ( k8_relset_1(A_14,B_15,C_16,D_17) = k10_relat_1(C_16,D_17)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_320,plain,(
    ! [B_89,C_90,D_91] :
      ( k8_relset_1('#skF_4',B_89,C_90,D_91) = k10_relat_1(C_90,D_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_28])).

tff(c_322,plain,(
    ! [B_89,D_91] : k8_relset_1('#skF_4',B_89,'#skF_4',D_91) = k10_relat_1('#skF_4',D_91) ),
    inference(resolution,[status(thm)],[c_179,c_320])).

tff(c_324,plain,(
    ! [B_89,D_91] : k8_relset_1('#skF_4',B_89,'#skF_4',D_91) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_322])).

tff(c_34,plain,(
    k8_relset_1(k1_xboole_0,'#skF_2','#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_176,plain,(
    k8_relset_1('#skF_4','#skF_2','#skF_4','#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_170,c_34])).

tff(c_327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_176])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:32:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.25  
% 2.16/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.25  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.16/1.25  
% 2.16/1.25  %Foreground sorts:
% 2.16/1.25  
% 2.16/1.25  
% 2.16/1.25  %Background operators:
% 2.16/1.25  
% 2.16/1.25  
% 2.16/1.25  %Foreground operators:
% 2.16/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.16/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.25  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.16/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.16/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.16/1.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.16/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.16/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.25  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.16/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.16/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.16/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.16/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.16/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.25  
% 2.16/1.26  tff(f_83, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 2.16/1.26  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.16/1.26  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.16/1.26  tff(f_92, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_xboole_0, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, A)))) => (k8_relset_1(k1_xboole_0, A, C, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_2)).
% 2.16/1.26  tff(f_47, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.16/1.26  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.16/1.26  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.16/1.26  tff(f_54, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.16/1.26  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 2.16/1.26  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.16/1.26  tff(f_62, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.16/1.26  tff(c_32, plain, (![A_18]: (r2_hidden('#skF_1'(A_18), A_18) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.16/1.26  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.16/1.26  tff(c_16, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.16/1.26  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.16/1.26  tff(c_41, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_36])).
% 2.16/1.26  tff(c_159, plain, (![C_60, B_61, A_62]: (~v1_xboole_0(C_60) | ~m1_subset_1(B_61, k1_zfmisc_1(C_60)) | ~r2_hidden(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.16/1.26  tff(c_161, plain, (![A_62]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_62, '#skF_4'))), inference(resolution, [status(thm)], [c_41, c_159])).
% 2.16/1.26  tff(c_165, plain, (![A_63]: (~r2_hidden(A_63, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_161])).
% 2.16/1.26  tff(c_170, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_32, c_165])).
% 2.16/1.26  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.16/1.26  tff(c_182, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_10])).
% 2.16/1.26  tff(c_76, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.16/1.26  tff(c_81, plain, (![C_48]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_76])).
% 2.16/1.26  tff(c_85, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_41, c_81])).
% 2.16/1.26  tff(c_128, plain, (![C_56, B_57, A_58]: (~v1_xboole_0(C_56) | ~m1_subset_1(B_57, k1_zfmisc_1(C_56)) | ~r2_hidden(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.16/1.27  tff(c_130, plain, (![A_58]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_58, '#skF_4'))), inference(resolution, [status(thm)], [c_41, c_128])).
% 2.16/1.27  tff(c_134, plain, (![A_59]: (~r2_hidden(A_59, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_130])).
% 2.16/1.27  tff(c_139, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_32, c_134])).
% 2.16/1.27  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.16/1.27  tff(c_120, plain, (![B_54, A_55]: (r1_tarski(k10_relat_1(B_54, A_55), k1_relat_1(B_54)) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.16/1.27  tff(c_125, plain, (![A_55]: (r1_tarski(k10_relat_1(k1_xboole_0, A_55), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_120])).
% 2.16/1.27  tff(c_127, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_125])).
% 2.16/1.27  tff(c_140, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_127])).
% 2.16/1.27  tff(c_156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_140])).
% 2.16/1.27  tff(c_157, plain, (![A_55]: (r1_tarski(k10_relat_1(k1_xboole_0, A_55), k1_xboole_0))), inference(splitRight, [status(thm)], [c_125])).
% 2.16/1.27  tff(c_244, plain, (![A_71]: (r1_tarski(k10_relat_1('#skF_4', A_71), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_170, c_157])).
% 2.16/1.27  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.16/1.27  tff(c_246, plain, (![A_71]: (k10_relat_1('#skF_4', A_71)='#skF_4' | ~r1_tarski('#skF_4', k10_relat_1('#skF_4', A_71)))), inference(resolution, [status(thm)], [c_244, c_4])).
% 2.16/1.27  tff(c_249, plain, (![A_71]: (k10_relat_1('#skF_4', A_71)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_246])).
% 2.16/1.27  tff(c_179, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_41])).
% 2.16/1.27  tff(c_219, plain, (![B_70]: (k2_zfmisc_1('#skF_4', B_70)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_170, c_16])).
% 2.16/1.27  tff(c_28, plain, (![A_14, B_15, C_16, D_17]: (k8_relset_1(A_14, B_15, C_16, D_17)=k10_relat_1(C_16, D_17) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.16/1.27  tff(c_320, plain, (![B_89, C_90, D_91]: (k8_relset_1('#skF_4', B_89, C_90, D_91)=k10_relat_1(C_90, D_91) | ~m1_subset_1(C_90, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_219, c_28])).
% 2.16/1.27  tff(c_322, plain, (![B_89, D_91]: (k8_relset_1('#skF_4', B_89, '#skF_4', D_91)=k10_relat_1('#skF_4', D_91))), inference(resolution, [status(thm)], [c_179, c_320])).
% 2.16/1.27  tff(c_324, plain, (![B_89, D_91]: (k8_relset_1('#skF_4', B_89, '#skF_4', D_91)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_249, c_322])).
% 2.16/1.27  tff(c_34, plain, (k8_relset_1(k1_xboole_0, '#skF_2', '#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.16/1.27  tff(c_176, plain, (k8_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_170, c_170, c_34])).
% 2.16/1.27  tff(c_327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_324, c_176])).
% 2.16/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.27  
% 2.16/1.27  Inference rules
% 2.16/1.27  ----------------------
% 2.16/1.27  #Ref     : 0
% 2.16/1.27  #Sup     : 59
% 2.16/1.27  #Fact    : 0
% 2.16/1.27  #Define  : 0
% 2.16/1.27  #Split   : 1
% 2.16/1.27  #Chain   : 0
% 2.16/1.27  #Close   : 0
% 2.16/1.27  
% 2.16/1.27  Ordering : KBO
% 2.16/1.27  
% 2.16/1.27  Simplification rules
% 2.16/1.27  ----------------------
% 2.16/1.27  #Subsume      : 5
% 2.16/1.27  #Demod        : 67
% 2.16/1.27  #Tautology    : 42
% 2.16/1.27  #SimpNegUnit  : 0
% 2.16/1.27  #BackRed      : 30
% 2.16/1.27  
% 2.16/1.27  #Partial instantiations: 0
% 2.16/1.27  #Strategies tried      : 1
% 2.16/1.27  
% 2.16/1.27  Timing (in seconds)
% 2.16/1.27  ----------------------
% 2.16/1.27  Preprocessing        : 0.32
% 2.16/1.27  Parsing              : 0.17
% 2.16/1.27  CNF conversion       : 0.02
% 2.16/1.27  Main loop            : 0.19
% 2.16/1.27  Inferencing          : 0.07
% 2.16/1.27  Reduction            : 0.06
% 2.16/1.27  Demodulation         : 0.05
% 2.16/1.27  BG Simplification    : 0.01
% 2.16/1.27  Subsumption          : 0.03
% 2.16/1.27  Abstraction          : 0.01
% 2.16/1.27  MUC search           : 0.00
% 2.16/1.27  Cooper               : 0.00
% 2.16/1.27  Total                : 0.54
% 2.16/1.27  Index Insertion      : 0.00
% 2.16/1.27  Index Deletion       : 0.00
% 2.16/1.27  Index Matching       : 0.00
% 2.16/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
