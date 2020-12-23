%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:27 EST 2020

% Result     : Theorem 4.22s
% Output     : CNFRefutation 4.22s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 143 expanded)
%              Number of leaves         :   36 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :  128 ( 345 expanded)
%              Number of equality atoms :   38 ( 115 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_6

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
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

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
      <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_98,axiom,(
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

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_120,plain,(
    ! [A_59,B_60,C_61] :
      ( k2_relset_1(A_59,B_60,C_61) = k2_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_129,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_120])).

tff(c_48,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_130,plain,(
    k2_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_48])).

tff(c_1712,plain,(
    ! [A_255,B_256,C_257] :
      ( r2_hidden('#skF_1'(A_255,B_256,C_257),B_256)
      | k2_relset_1(A_255,B_256,C_257) = B_256
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1723,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_1712])).

tff(c_1729,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_1723])).

tff(c_1730,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_1729])).

tff(c_58,plain,(
    ! [D_42] :
      ( r2_hidden('#skF_6'(D_42),'#skF_3')
      | ~ r2_hidden(D_42,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_52,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_158,plain,(
    ! [A_64,B_65,C_66] :
      ( k1_relset_1(A_64,B_65,C_66) = k1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_167,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_158])).

tff(c_1662,plain,(
    ! [B_247,A_248,C_249] :
      ( k1_xboole_0 = B_247
      | k1_relset_1(A_248,B_247,C_249) = A_248
      | ~ v1_funct_2(C_249,A_248,B_247)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(A_248,B_247))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1677,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1662])).

tff(c_1684,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_167,c_1677])).

tff(c_1685,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1684])).

tff(c_16,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_109,plain,(
    ! [B_57,A_58] :
      ( v1_relat_1(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_115,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_50,c_109])).

tff(c_119,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_115])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_56,plain,(
    ! [D_42] :
      ( k1_funct_1('#skF_5','#skF_6'(D_42)) = D_42
      | ~ r2_hidden(D_42,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1376,plain,(
    ! [A_215,C_216] :
      ( r2_hidden(k4_tarski(A_215,k1_funct_1(C_216,A_215)),C_216)
      | ~ r2_hidden(A_215,k1_relat_1(C_216))
      | ~ v1_funct_1(C_216)
      | ~ v1_relat_1(C_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1385,plain,(
    ! [D_42] :
      ( r2_hidden(k4_tarski('#skF_6'(D_42),D_42),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_42),k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden(D_42,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1376])).

tff(c_1390,plain,(
    ! [D_42] :
      ( r2_hidden(k4_tarski('#skF_6'(D_42),D_42),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_42),k1_relat_1('#skF_5'))
      | ~ r2_hidden(D_42,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_54,c_1385])).

tff(c_1686,plain,(
    ! [D_42] :
      ( r2_hidden(k4_tarski('#skF_6'(D_42),D_42),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_42),'#skF_3')
      | ~ r2_hidden(D_42,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1685,c_1390])).

tff(c_1840,plain,(
    ! [E_272,A_273,B_274,C_275] :
      ( ~ r2_hidden(k4_tarski(E_272,'#skF_1'(A_273,B_274,C_275)),C_275)
      | k2_relset_1(A_273,B_274,C_275) = B_274
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(A_273,B_274))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1927,plain,(
    ! [A_281,B_282] :
      ( k2_relset_1(A_281,B_282,'#skF_5') = B_282
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_281,B_282)))
      | ~ r2_hidden('#skF_6'('#skF_1'(A_281,B_282,'#skF_5')),'#skF_3')
      | ~ r2_hidden('#skF_1'(A_281,B_282,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1686,c_1840])).

tff(c_2147,plain,(
    ! [A_309,B_310] :
      ( k2_relset_1(A_309,B_310,'#skF_5') = B_310
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_309,B_310)))
      | ~ r2_hidden('#skF_1'(A_309,B_310,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_1927])).

tff(c_2153,plain,
    ( k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4'
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_2147])).

tff(c_2157,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1730,c_129,c_2153])).

tff(c_2159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_2157])).

tff(c_2160,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1684])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2181,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2160,c_8])).

tff(c_245,plain,(
    ! [A_86,B_87,C_88] :
      ( m1_subset_1(k2_relset_1(A_86,B_87,C_88),k1_zfmisc_1(B_87))
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_268,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_245])).

tff(c_274,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_268])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_282,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_274,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_287,plain,
    ( k2_relat_1('#skF_5') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_282,c_2])).

tff(c_291,plain,(
    ~ r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_287])).

tff(c_2189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2181,c_291])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.31  % Computer   : n007.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % DateTime   : Tue Dec  1 15:20:36 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.16/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.22/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.22/1.69  
% 4.22/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.22/1.69  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_6
% 4.22/1.69  
% 4.22/1.69  %Foreground sorts:
% 4.22/1.69  
% 4.22/1.69  
% 4.22/1.69  %Background operators:
% 4.22/1.69  
% 4.22/1.69  
% 4.22/1.69  %Foreground operators:
% 4.22/1.69  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.22/1.69  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.22/1.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.22/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.22/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.22/1.69  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.22/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.22/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.22/1.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.22/1.69  tff('#skF_5', type, '#skF_5': $i).
% 4.22/1.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.22/1.69  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.22/1.69  tff('#skF_3', type, '#skF_3': $i).
% 4.22/1.69  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.22/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.22/1.69  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.22/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.22/1.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.22/1.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.22/1.69  tff('#skF_4', type, '#skF_4': $i).
% 4.22/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.22/1.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.22/1.69  tff('#skF_6', type, '#skF_6': $i > $i).
% 4.22/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.22/1.69  
% 4.22/1.70  tff(f_117, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 4.22/1.70  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.22/1.70  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relset_1)).
% 4.22/1.70  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.22/1.70  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.22/1.70  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.22/1.70  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.22/1.70  tff(f_56, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 4.22/1.70  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.22/1.70  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.22/1.70  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.22/1.70  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.22/1.70  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.22/1.70  tff(c_120, plain, (![A_59, B_60, C_61]: (k2_relset_1(A_59, B_60, C_61)=k2_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.22/1.70  tff(c_129, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_120])).
% 4.22/1.70  tff(c_48, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.22/1.70  tff(c_130, plain, (k2_relat_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_48])).
% 4.22/1.70  tff(c_1712, plain, (![A_255, B_256, C_257]: (r2_hidden('#skF_1'(A_255, B_256, C_257), B_256) | k2_relset_1(A_255, B_256, C_257)=B_256 | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.22/1.70  tff(c_1723, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_50, c_1712])).
% 4.22/1.70  tff(c_1729, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_1723])).
% 4.22/1.70  tff(c_1730, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_130, c_1729])).
% 4.22/1.70  tff(c_58, plain, (![D_42]: (r2_hidden('#skF_6'(D_42), '#skF_3') | ~r2_hidden(D_42, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.22/1.70  tff(c_52, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.22/1.70  tff(c_158, plain, (![A_64, B_65, C_66]: (k1_relset_1(A_64, B_65, C_66)=k1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.22/1.70  tff(c_167, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_158])).
% 4.22/1.70  tff(c_1662, plain, (![B_247, A_248, C_249]: (k1_xboole_0=B_247 | k1_relset_1(A_248, B_247, C_249)=A_248 | ~v1_funct_2(C_249, A_248, B_247) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(A_248, B_247))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.22/1.70  tff(c_1677, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_1662])).
% 4.22/1.70  tff(c_1684, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_167, c_1677])).
% 4.22/1.70  tff(c_1685, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_1684])).
% 4.22/1.70  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.22/1.70  tff(c_109, plain, (![B_57, A_58]: (v1_relat_1(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.22/1.70  tff(c_115, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_109])).
% 4.22/1.70  tff(c_119, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_115])).
% 4.22/1.70  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.22/1.70  tff(c_56, plain, (![D_42]: (k1_funct_1('#skF_5', '#skF_6'(D_42))=D_42 | ~r2_hidden(D_42, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.22/1.70  tff(c_1376, plain, (![A_215, C_216]: (r2_hidden(k4_tarski(A_215, k1_funct_1(C_216, A_215)), C_216) | ~r2_hidden(A_215, k1_relat_1(C_216)) | ~v1_funct_1(C_216) | ~v1_relat_1(C_216))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.22/1.70  tff(c_1385, plain, (![D_42]: (r2_hidden(k4_tarski('#skF_6'(D_42), D_42), '#skF_5') | ~r2_hidden('#skF_6'(D_42), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden(D_42, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1376])).
% 4.22/1.70  tff(c_1390, plain, (![D_42]: (r2_hidden(k4_tarski('#skF_6'(D_42), D_42), '#skF_5') | ~r2_hidden('#skF_6'(D_42), k1_relat_1('#skF_5')) | ~r2_hidden(D_42, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_54, c_1385])).
% 4.22/1.70  tff(c_1686, plain, (![D_42]: (r2_hidden(k4_tarski('#skF_6'(D_42), D_42), '#skF_5') | ~r2_hidden('#skF_6'(D_42), '#skF_3') | ~r2_hidden(D_42, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1685, c_1390])).
% 4.22/1.70  tff(c_1840, plain, (![E_272, A_273, B_274, C_275]: (~r2_hidden(k4_tarski(E_272, '#skF_1'(A_273, B_274, C_275)), C_275) | k2_relset_1(A_273, B_274, C_275)=B_274 | ~m1_subset_1(C_275, k1_zfmisc_1(k2_zfmisc_1(A_273, B_274))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.22/1.70  tff(c_1927, plain, (![A_281, B_282]: (k2_relset_1(A_281, B_282, '#skF_5')=B_282 | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_281, B_282))) | ~r2_hidden('#skF_6'('#skF_1'(A_281, B_282, '#skF_5')), '#skF_3') | ~r2_hidden('#skF_1'(A_281, B_282, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_1686, c_1840])).
% 4.22/1.70  tff(c_2147, plain, (![A_309, B_310]: (k2_relset_1(A_309, B_310, '#skF_5')=B_310 | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_309, B_310))) | ~r2_hidden('#skF_1'(A_309, B_310, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_1927])).
% 4.22/1.70  tff(c_2153, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4' | ~r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_50, c_2147])).
% 4.22/1.70  tff(c_2157, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1730, c_129, c_2153])).
% 4.22/1.70  tff(c_2159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_2157])).
% 4.22/1.70  tff(c_2160, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1684])).
% 4.22/1.70  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.22/1.70  tff(c_2181, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2160, c_8])).
% 4.22/1.70  tff(c_245, plain, (![A_86, B_87, C_88]: (m1_subset_1(k2_relset_1(A_86, B_87, C_88), k1_zfmisc_1(B_87)) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.22/1.70  tff(c_268, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_129, c_245])).
% 4.22/1.70  tff(c_274, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_268])).
% 4.22/1.70  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.22/1.70  tff(c_282, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_274, c_10])).
% 4.22/1.70  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.22/1.70  tff(c_287, plain, (k2_relat_1('#skF_5')='#skF_4' | ~r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_282, c_2])).
% 4.22/1.70  tff(c_291, plain, (~r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_130, c_287])).
% 4.22/1.70  tff(c_2189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2181, c_291])).
% 4.22/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.22/1.70  
% 4.22/1.70  Inference rules
% 4.22/1.70  ----------------------
% 4.22/1.70  #Ref     : 0
% 4.22/1.70  #Sup     : 406
% 4.22/1.70  #Fact    : 0
% 4.22/1.70  #Define  : 0
% 4.22/1.70  #Split   : 7
% 4.22/1.70  #Chain   : 0
% 4.22/1.70  #Close   : 0
% 4.22/1.70  
% 4.22/1.70  Ordering : KBO
% 4.22/1.70  
% 4.22/1.70  Simplification rules
% 4.22/1.70  ----------------------
% 4.22/1.70  #Subsume      : 44
% 4.22/1.70  #Demod        : 366
% 4.22/1.70  #Tautology    : 173
% 4.22/1.70  #SimpNegUnit  : 18
% 4.22/1.70  #BackRed      : 58
% 4.22/1.70  
% 4.22/1.70  #Partial instantiations: 0
% 4.22/1.70  #Strategies tried      : 1
% 4.22/1.70  
% 4.22/1.70  Timing (in seconds)
% 4.22/1.70  ----------------------
% 4.22/1.71  Preprocessing        : 0.33
% 4.22/1.71  Parsing              : 0.17
% 4.22/1.71  CNF conversion       : 0.02
% 4.22/1.71  Main loop            : 0.63
% 4.22/1.71  Inferencing          : 0.23
% 4.22/1.71  Reduction            : 0.20
% 4.22/1.71  Demodulation         : 0.14
% 4.22/1.71  BG Simplification    : 0.03
% 4.22/1.71  Subsumption          : 0.11
% 4.22/1.71  Abstraction          : 0.04
% 4.22/1.71  MUC search           : 0.00
% 4.22/1.71  Cooper               : 0.00
% 4.22/1.71  Total                : 0.99
% 4.22/1.71  Index Insertion      : 0.00
% 4.22/1.71  Index Deletion       : 0.00
% 4.22/1.71  Index Matching       : 0.00
% 4.22/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
