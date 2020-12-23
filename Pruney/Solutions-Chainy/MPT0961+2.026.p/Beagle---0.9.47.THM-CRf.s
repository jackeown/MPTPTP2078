%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:45 EST 2020

% Result     : Theorem 5.37s
% Output     : CNFRefutation 5.37s
% Verified   : 
% Statistics : Number of formulae       :  125 (1321 expanded)
%              Number of leaves         :   32 ( 456 expanded)
%              Depth                    :   13
%              Number of atoms          :  240 (2849 expanded)
%              Number of equality atoms :   61 ( 592 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_34,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_75,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_44,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_8,plain,(
    ! [A_5] : k2_subset_1(A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [A_6] : m1_subset_1(k2_subset_1(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_47,plain,(
    ! [A_6] : m1_subset_1(A_6,k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_2927,plain,(
    ! [A_346,B_347] :
      ( r1_tarski(A_346,B_347)
      | ~ m1_subset_1(A_346,k1_zfmisc_1(B_347)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2931,plain,(
    ! [A_6] : r1_tarski(A_6,A_6) ),
    inference(resolution,[status(thm)],[c_47,c_2927])).

tff(c_3291,plain,(
    ! [C_410,A_411,B_412] :
      ( m1_subset_1(C_410,k1_zfmisc_1(k2_zfmisc_1(A_411,B_412)))
      | ~ r1_tarski(k2_relat_1(C_410),B_412)
      | ~ r1_tarski(k1_relat_1(C_410),A_411)
      | ~ v1_relat_1(C_410) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | ~ m1_subset_1(A_39,k1_zfmisc_1(B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_80,plain,(
    ! [A_6] : r1_tarski(A_6,A_6) ),
    inference(resolution,[status(thm)],[c_47,c_76])).

tff(c_1487,plain,(
    ! [C_211,A_212,B_213] :
      ( m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_212,B_213)))
      | ~ r1_tarski(k2_relat_1(C_211),B_213)
      | ~ r1_tarski(k1_relat_1(C_211),A_212)
      | ~ v1_relat_1(C_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1713,plain,(
    ! [C_239,A_240,B_241] :
      ( r1_tarski(C_239,k2_zfmisc_1(A_240,B_241))
      | ~ r1_tarski(k2_relat_1(C_239),B_241)
      | ~ r1_tarski(k1_relat_1(C_239),A_240)
      | ~ v1_relat_1(C_239) ) ),
    inference(resolution,[status(thm)],[c_1487,c_12])).

tff(c_1718,plain,(
    ! [C_242,A_243] :
      ( r1_tarski(C_242,k2_zfmisc_1(A_243,k2_relat_1(C_242)))
      | ~ r1_tarski(k1_relat_1(C_242),A_243)
      | ~ v1_relat_1(C_242) ) ),
    inference(resolution,[status(thm)],[c_80,c_1713])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_210,plain,(
    ! [A_75,B_76,C_77] :
      ( k1_relset_1(A_75,B_76,C_77) = k1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_225,plain,(
    ! [A_75,B_76,A_7] :
      ( k1_relset_1(A_75,B_76,A_7) = k1_relat_1(A_7)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_75,B_76)) ) ),
    inference(resolution,[status(thm)],[c_14,c_210])).

tff(c_1745,plain,(
    ! [A_244,C_245] :
      ( k1_relset_1(A_244,k2_relat_1(C_245),C_245) = k1_relat_1(C_245)
      | ~ r1_tarski(k1_relat_1(C_245),A_244)
      | ~ v1_relat_1(C_245) ) ),
    inference(resolution,[status(thm)],[c_1718,c_225])).

tff(c_1756,plain,(
    ! [C_245] :
      ( k1_relset_1(k1_relat_1(C_245),k2_relat_1(C_245),C_245) = k1_relat_1(C_245)
      | ~ v1_relat_1(C_245) ) ),
    inference(resolution,[status(thm)],[c_80,c_1745])).

tff(c_1717,plain,(
    ! [C_239,A_240] :
      ( r1_tarski(C_239,k2_zfmisc_1(A_240,k2_relat_1(C_239)))
      | ~ r1_tarski(k1_relat_1(C_239),A_240)
      | ~ v1_relat_1(C_239) ) ),
    inference(resolution,[status(thm)],[c_80,c_1713])).

tff(c_1641,plain,(
    ! [B_230,C_231,A_232] :
      ( k1_xboole_0 = B_230
      | v1_funct_2(C_231,A_232,B_230)
      | k1_relset_1(A_232,B_230,C_231) != A_232
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_232,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2384,plain,(
    ! [B_305,A_306,A_307] :
      ( k1_xboole_0 = B_305
      | v1_funct_2(A_306,A_307,B_305)
      | k1_relset_1(A_307,B_305,A_306) != A_307
      | ~ r1_tarski(A_306,k2_zfmisc_1(A_307,B_305)) ) ),
    inference(resolution,[status(thm)],[c_14,c_1641])).

tff(c_2606,plain,(
    ! [C_335,A_336] :
      ( k2_relat_1(C_335) = k1_xboole_0
      | v1_funct_2(C_335,A_336,k2_relat_1(C_335))
      | k1_relset_1(A_336,k2_relat_1(C_335),C_335) != A_336
      | ~ r1_tarski(k1_relat_1(C_335),A_336)
      | ~ v1_relat_1(C_335) ) ),
    inference(resolution,[status(thm)],[c_1717,c_2384])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_40,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40])).

tff(c_75,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_2613,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2606,c_75])).

tff(c_2617,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_80,c_2613])).

tff(c_2618,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2617])).

tff(c_2667,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1756,c_2618])).

tff(c_2671,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2667])).

tff(c_2672,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2617])).

tff(c_16,plain,(
    ! [C_12,B_10,A_9] :
      ( v1_xboole_0(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(B_10,A_9)))
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1626,plain,(
    ! [C_224,B_225,A_226] :
      ( v1_xboole_0(C_224)
      | ~ v1_xboole_0(B_225)
      | ~ r1_tarski(k2_relat_1(C_224),B_225)
      | ~ r1_tarski(k1_relat_1(C_224),A_226)
      | ~ v1_relat_1(C_224) ) ),
    inference(resolution,[status(thm)],[c_1487,c_16])).

tff(c_1631,plain,(
    ! [C_227,A_228] :
      ( v1_xboole_0(C_227)
      | ~ v1_xboole_0(k2_relat_1(C_227))
      | ~ r1_tarski(k1_relat_1(C_227),A_228)
      | ~ v1_relat_1(C_227) ) ),
    inference(resolution,[status(thm)],[c_80,c_1626])).

tff(c_1639,plain,(
    ! [C_227] :
      ( v1_xboole_0(C_227)
      | ~ v1_xboole_0(k2_relat_1(C_227))
      | ~ v1_relat_1(C_227) ) ),
    inference(resolution,[status(thm)],[c_80,c_1631])).

tff(c_2707,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2672,c_1639])).

tff(c_2735,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6,c_2707])).

tff(c_59,plain,(
    ! [A_36] :
      ( r2_hidden('#skF_2'(A_36),A_36)
      | k1_xboole_0 = A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(A_36)
      | k1_xboole_0 = A_36 ) ),
    inference(resolution,[status(thm)],[c_59,c_2])).

tff(c_2745,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2735,c_63])).

tff(c_476,plain,(
    ! [C_110,A_111,B_112] :
      ( m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112)))
      | ~ r1_tarski(k2_relat_1(C_110),B_112)
      | ~ r1_tarski(k1_relat_1(C_110),A_111)
      | ~ v1_relat_1(C_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_690,plain,(
    ! [C_139,A_140,B_141] :
      ( r1_tarski(C_139,k2_zfmisc_1(A_140,B_141))
      | ~ r1_tarski(k2_relat_1(C_139),B_141)
      | ~ r1_tarski(k1_relat_1(C_139),A_140)
      | ~ v1_relat_1(C_139) ) ),
    inference(resolution,[status(thm)],[c_476,c_12])).

tff(c_695,plain,(
    ! [C_142,A_143] :
      ( r1_tarski(C_142,k2_zfmisc_1(A_143,k2_relat_1(C_142)))
      | ~ r1_tarski(k1_relat_1(C_142),A_143)
      | ~ v1_relat_1(C_142) ) ),
    inference(resolution,[status(thm)],[c_80,c_690])).

tff(c_722,plain,(
    ! [A_144,C_145] :
      ( k1_relset_1(A_144,k2_relat_1(C_145),C_145) = k1_relat_1(C_145)
      | ~ r1_tarski(k1_relat_1(C_145),A_144)
      | ~ v1_relat_1(C_145) ) ),
    inference(resolution,[status(thm)],[c_695,c_225])).

tff(c_732,plain,(
    ! [C_145] :
      ( k1_relset_1(k1_relat_1(C_145),k2_relat_1(C_145),C_145) = k1_relat_1(C_145)
      | ~ v1_relat_1(C_145) ) ),
    inference(resolution,[status(thm)],[c_80,c_722])).

tff(c_20,plain,(
    ! [C_18,A_16,B_17] :
      ( m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17)))
      | ~ r1_tarski(k2_relat_1(C_18),B_17)
      | ~ r1_tarski(k1_relat_1(C_18),A_16)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_567,plain,(
    ! [B_123,C_124,A_125] :
      ( k1_xboole_0 = B_123
      | v1_funct_2(C_124,A_125,B_123)
      | k1_relset_1(A_125,B_123,C_124) != A_125
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_125,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1011,plain,(
    ! [B_185,C_186,A_187] :
      ( k1_xboole_0 = B_185
      | v1_funct_2(C_186,A_187,B_185)
      | k1_relset_1(A_187,B_185,C_186) != A_187
      | ~ r1_tarski(k2_relat_1(C_186),B_185)
      | ~ r1_tarski(k1_relat_1(C_186),A_187)
      | ~ v1_relat_1(C_186) ) ),
    inference(resolution,[status(thm)],[c_20,c_567])).

tff(c_1117,plain,(
    ! [C_197,A_198] :
      ( k2_relat_1(C_197) = k1_xboole_0
      | v1_funct_2(C_197,A_198,k2_relat_1(C_197))
      | k1_relset_1(A_198,k2_relat_1(C_197),C_197) != A_198
      | ~ r1_tarski(k1_relat_1(C_197),A_198)
      | ~ v1_relat_1(C_197) ) ),
    inference(resolution,[status(thm)],[c_80,c_1011])).

tff(c_1126,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1117,c_75])).

tff(c_1133,plain,
    ( k2_relat_1('#skF_3') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_80,c_1126])).

tff(c_1134,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1133])).

tff(c_1137,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_732,c_1134])).

tff(c_1141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1137])).

tff(c_1142,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1133])).

tff(c_557,plain,(
    ! [C_118,B_119,A_120] :
      ( v1_xboole_0(C_118)
      | ~ v1_xboole_0(B_119)
      | ~ r1_tarski(k2_relat_1(C_118),B_119)
      | ~ r1_tarski(k1_relat_1(C_118),A_120)
      | ~ v1_relat_1(C_118) ) ),
    inference(resolution,[status(thm)],[c_476,c_16])).

tff(c_562,plain,(
    ! [C_121,A_122] :
      ( v1_xboole_0(C_121)
      | ~ v1_xboole_0(k2_relat_1(C_121))
      | ~ r1_tarski(k1_relat_1(C_121),A_122)
      | ~ v1_relat_1(C_121) ) ),
    inference(resolution,[status(thm)],[c_80,c_557])).

tff(c_566,plain,(
    ! [C_121] :
      ( v1_xboole_0(C_121)
      | ~ v1_xboole_0(k2_relat_1(C_121))
      | ~ v1_relat_1(C_121) ) ),
    inference(resolution,[status(thm)],[c_80,c_562])).

tff(c_1179,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1142,c_566])).

tff(c_1209,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6,c_1179])).

tff(c_1219,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1209,c_63])).

tff(c_87,plain,(
    ! [C_44,B_45,A_46] :
      ( v1_xboole_0(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(B_45,A_46)))
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_105,plain,(
    ! [B_50,A_51] :
      ( v1_xboole_0(k2_zfmisc_1(B_50,A_51))
      | ~ v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_47,c_87])).

tff(c_110,plain,(
    ! [B_52,A_53] :
      ( k2_zfmisc_1(B_52,A_53) = k1_xboole_0
      | ~ v1_xboole_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_105,c_63])).

tff(c_116,plain,(
    ! [B_52] : k2_zfmisc_1(B_52,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_110])).

tff(c_226,plain,(
    ! [A_75,B_76] : k1_relset_1(A_75,B_76,k2_zfmisc_1(A_75,B_76)) = k1_relat_1(k2_zfmisc_1(A_75,B_76)) ),
    inference(resolution,[status(thm)],[c_47,c_210])).

tff(c_354,plain,(
    ! [C_101,B_102] :
      ( v1_funct_2(C_101,k1_xboole_0,B_102)
      | k1_relset_1(k1_xboole_0,B_102,C_101) != k1_xboole_0
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_370,plain,(
    ! [B_102] :
      ( v1_funct_2(k2_zfmisc_1(k1_xboole_0,B_102),k1_xboole_0,B_102)
      | k1_relset_1(k1_xboole_0,B_102,k2_zfmisc_1(k1_xboole_0,B_102)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_47,c_354])).

tff(c_374,plain,(
    ! [B_103] :
      ( v1_funct_2(k2_zfmisc_1(k1_xboole_0,B_103),k1_xboole_0,B_103)
      | k1_relat_1(k2_zfmisc_1(k1_xboole_0,B_103)) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_370])).

tff(c_385,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_374])).

tff(c_390,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_385])).

tff(c_391,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_390])).

tff(c_1256,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1219,c_1219,c_391])).

tff(c_28,plain,(
    ! [A_29] :
      ( v1_funct_2(k1_xboole_0,A_29,k1_xboole_0)
      | k1_xboole_0 = A_29
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_29,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_192,plain,(
    ! [A_29] :
      ( v1_funct_2(k1_xboole_0,A_29,k1_xboole_0)
      | k1_xboole_0 = A_29 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_116,c_28])).

tff(c_1376,plain,(
    ! [A_202] :
      ( v1_funct_2('#skF_3',A_202,'#skF_3')
      | A_202 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1219,c_1219,c_1219,c_192])).

tff(c_1144,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1142,c_75])).

tff(c_1220,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1219,c_1144])).

tff(c_1382,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1376,c_1220])).

tff(c_1388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1256,c_1382])).

tff(c_1389,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_390])).

tff(c_2780,plain,(
    v1_funct_2('#skF_3','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2745,c_2745,c_2745,c_1389])).

tff(c_1390,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_390])).

tff(c_2782,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2745,c_2745,c_1390])).

tff(c_2674,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2672,c_75])).

tff(c_2746,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2745,c_2674])).

tff(c_2924,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2780,c_2782,c_2746])).

tff(c_2925,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_3308,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3291,c_2925])).

tff(c_3325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2931,c_2931,c_3308])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:53:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.37/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.37/2.00  
% 5.37/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.37/2.00  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3
% 5.37/2.00  
% 5.37/2.00  %Foreground sorts:
% 5.37/2.00  
% 5.37/2.00  
% 5.37/2.00  %Background operators:
% 5.37/2.00  
% 5.37/2.00  
% 5.37/2.00  %Foreground operators:
% 5.37/2.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.37/2.00  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.37/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.37/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.37/2.00  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.37/2.00  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.37/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.37/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.37/2.00  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.37/2.00  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.37/2.00  tff('#skF_3', type, '#skF_3': $i).
% 5.37/2.00  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.37/2.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.37/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.37/2.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.37/2.00  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.37/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.37/2.00  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.37/2.00  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.37/2.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.37/2.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.37/2.00  
% 5.37/2.02  tff(f_104, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 5.37/2.02  tff(f_34, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.37/2.02  tff(f_36, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.37/2.02  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.37/2.02  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 5.37/2.02  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.37/2.02  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.37/2.02  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.37/2.02  tff(f_47, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 5.37/2.02  tff(f_75, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 5.37/2.02  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.37/2.02  tff(c_44, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.37/2.02  tff(c_8, plain, (![A_5]: (k2_subset_1(A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.37/2.02  tff(c_10, plain, (![A_6]: (m1_subset_1(k2_subset_1(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.37/2.02  tff(c_47, plain, (![A_6]: (m1_subset_1(A_6, k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 5.37/2.02  tff(c_2927, plain, (![A_346, B_347]: (r1_tarski(A_346, B_347) | ~m1_subset_1(A_346, k1_zfmisc_1(B_347)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.37/2.02  tff(c_2931, plain, (![A_6]: (r1_tarski(A_6, A_6))), inference(resolution, [status(thm)], [c_47, c_2927])).
% 5.37/2.02  tff(c_3291, plain, (![C_410, A_411, B_412]: (m1_subset_1(C_410, k1_zfmisc_1(k2_zfmisc_1(A_411, B_412))) | ~r1_tarski(k2_relat_1(C_410), B_412) | ~r1_tarski(k1_relat_1(C_410), A_411) | ~v1_relat_1(C_410))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.37/2.02  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.37/2.02  tff(c_76, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | ~m1_subset_1(A_39, k1_zfmisc_1(B_40)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.37/2.02  tff(c_80, plain, (![A_6]: (r1_tarski(A_6, A_6))), inference(resolution, [status(thm)], [c_47, c_76])).
% 5.37/2.02  tff(c_1487, plain, (![C_211, A_212, B_213]: (m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_212, B_213))) | ~r1_tarski(k2_relat_1(C_211), B_213) | ~r1_tarski(k1_relat_1(C_211), A_212) | ~v1_relat_1(C_211))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.37/2.02  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.37/2.02  tff(c_1713, plain, (![C_239, A_240, B_241]: (r1_tarski(C_239, k2_zfmisc_1(A_240, B_241)) | ~r1_tarski(k2_relat_1(C_239), B_241) | ~r1_tarski(k1_relat_1(C_239), A_240) | ~v1_relat_1(C_239))), inference(resolution, [status(thm)], [c_1487, c_12])).
% 5.37/2.02  tff(c_1718, plain, (![C_242, A_243]: (r1_tarski(C_242, k2_zfmisc_1(A_243, k2_relat_1(C_242))) | ~r1_tarski(k1_relat_1(C_242), A_243) | ~v1_relat_1(C_242))), inference(resolution, [status(thm)], [c_80, c_1713])).
% 5.37/2.02  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.37/2.02  tff(c_210, plain, (![A_75, B_76, C_77]: (k1_relset_1(A_75, B_76, C_77)=k1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.37/2.02  tff(c_225, plain, (![A_75, B_76, A_7]: (k1_relset_1(A_75, B_76, A_7)=k1_relat_1(A_7) | ~r1_tarski(A_7, k2_zfmisc_1(A_75, B_76)))), inference(resolution, [status(thm)], [c_14, c_210])).
% 5.37/2.02  tff(c_1745, plain, (![A_244, C_245]: (k1_relset_1(A_244, k2_relat_1(C_245), C_245)=k1_relat_1(C_245) | ~r1_tarski(k1_relat_1(C_245), A_244) | ~v1_relat_1(C_245))), inference(resolution, [status(thm)], [c_1718, c_225])).
% 5.37/2.02  tff(c_1756, plain, (![C_245]: (k1_relset_1(k1_relat_1(C_245), k2_relat_1(C_245), C_245)=k1_relat_1(C_245) | ~v1_relat_1(C_245))), inference(resolution, [status(thm)], [c_80, c_1745])).
% 5.37/2.02  tff(c_1717, plain, (![C_239, A_240]: (r1_tarski(C_239, k2_zfmisc_1(A_240, k2_relat_1(C_239))) | ~r1_tarski(k1_relat_1(C_239), A_240) | ~v1_relat_1(C_239))), inference(resolution, [status(thm)], [c_80, c_1713])).
% 5.37/2.02  tff(c_1641, plain, (![B_230, C_231, A_232]: (k1_xboole_0=B_230 | v1_funct_2(C_231, A_232, B_230) | k1_relset_1(A_232, B_230, C_231)!=A_232 | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_232, B_230))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.37/2.02  tff(c_2384, plain, (![B_305, A_306, A_307]: (k1_xboole_0=B_305 | v1_funct_2(A_306, A_307, B_305) | k1_relset_1(A_307, B_305, A_306)!=A_307 | ~r1_tarski(A_306, k2_zfmisc_1(A_307, B_305)))), inference(resolution, [status(thm)], [c_14, c_1641])).
% 5.37/2.02  tff(c_2606, plain, (![C_335, A_336]: (k2_relat_1(C_335)=k1_xboole_0 | v1_funct_2(C_335, A_336, k2_relat_1(C_335)) | k1_relset_1(A_336, k2_relat_1(C_335), C_335)!=A_336 | ~r1_tarski(k1_relat_1(C_335), A_336) | ~v1_relat_1(C_335))), inference(resolution, [status(thm)], [c_1717, c_2384])).
% 5.37/2.02  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.37/2.02  tff(c_40, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.37/2.02  tff(c_46, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40])).
% 5.37/2.02  tff(c_75, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_46])).
% 5.37/2.02  tff(c_2613, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2606, c_75])).
% 5.37/2.02  tff(c_2617, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_80, c_2613])).
% 5.37/2.02  tff(c_2618, plain, (k1_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_2617])).
% 5.37/2.02  tff(c_2667, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1756, c_2618])).
% 5.37/2.02  tff(c_2671, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_2667])).
% 5.37/2.02  tff(c_2672, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2617])).
% 5.37/2.02  tff(c_16, plain, (![C_12, B_10, A_9]: (v1_xboole_0(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(B_10, A_9))) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.37/2.02  tff(c_1626, plain, (![C_224, B_225, A_226]: (v1_xboole_0(C_224) | ~v1_xboole_0(B_225) | ~r1_tarski(k2_relat_1(C_224), B_225) | ~r1_tarski(k1_relat_1(C_224), A_226) | ~v1_relat_1(C_224))), inference(resolution, [status(thm)], [c_1487, c_16])).
% 5.37/2.02  tff(c_1631, plain, (![C_227, A_228]: (v1_xboole_0(C_227) | ~v1_xboole_0(k2_relat_1(C_227)) | ~r1_tarski(k1_relat_1(C_227), A_228) | ~v1_relat_1(C_227))), inference(resolution, [status(thm)], [c_80, c_1626])).
% 5.37/2.02  tff(c_1639, plain, (![C_227]: (v1_xboole_0(C_227) | ~v1_xboole_0(k2_relat_1(C_227)) | ~v1_relat_1(C_227))), inference(resolution, [status(thm)], [c_80, c_1631])).
% 5.37/2.02  tff(c_2707, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2672, c_1639])).
% 5.37/2.02  tff(c_2735, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6, c_2707])).
% 5.37/2.02  tff(c_59, plain, (![A_36]: (r2_hidden('#skF_2'(A_36), A_36) | k1_xboole_0=A_36)), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.37/2.02  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.37/2.02  tff(c_63, plain, (![A_36]: (~v1_xboole_0(A_36) | k1_xboole_0=A_36)), inference(resolution, [status(thm)], [c_59, c_2])).
% 5.37/2.02  tff(c_2745, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2735, c_63])).
% 5.37/2.02  tff(c_476, plain, (![C_110, A_111, B_112]: (m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))) | ~r1_tarski(k2_relat_1(C_110), B_112) | ~r1_tarski(k1_relat_1(C_110), A_111) | ~v1_relat_1(C_110))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.37/2.02  tff(c_690, plain, (![C_139, A_140, B_141]: (r1_tarski(C_139, k2_zfmisc_1(A_140, B_141)) | ~r1_tarski(k2_relat_1(C_139), B_141) | ~r1_tarski(k1_relat_1(C_139), A_140) | ~v1_relat_1(C_139))), inference(resolution, [status(thm)], [c_476, c_12])).
% 5.37/2.02  tff(c_695, plain, (![C_142, A_143]: (r1_tarski(C_142, k2_zfmisc_1(A_143, k2_relat_1(C_142))) | ~r1_tarski(k1_relat_1(C_142), A_143) | ~v1_relat_1(C_142))), inference(resolution, [status(thm)], [c_80, c_690])).
% 5.37/2.02  tff(c_722, plain, (![A_144, C_145]: (k1_relset_1(A_144, k2_relat_1(C_145), C_145)=k1_relat_1(C_145) | ~r1_tarski(k1_relat_1(C_145), A_144) | ~v1_relat_1(C_145))), inference(resolution, [status(thm)], [c_695, c_225])).
% 5.37/2.02  tff(c_732, plain, (![C_145]: (k1_relset_1(k1_relat_1(C_145), k2_relat_1(C_145), C_145)=k1_relat_1(C_145) | ~v1_relat_1(C_145))), inference(resolution, [status(thm)], [c_80, c_722])).
% 5.37/2.02  tff(c_20, plain, (![C_18, A_16, B_17]: (m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))) | ~r1_tarski(k2_relat_1(C_18), B_17) | ~r1_tarski(k1_relat_1(C_18), A_16) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.37/2.02  tff(c_567, plain, (![B_123, C_124, A_125]: (k1_xboole_0=B_123 | v1_funct_2(C_124, A_125, B_123) | k1_relset_1(A_125, B_123, C_124)!=A_125 | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_125, B_123))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.37/2.02  tff(c_1011, plain, (![B_185, C_186, A_187]: (k1_xboole_0=B_185 | v1_funct_2(C_186, A_187, B_185) | k1_relset_1(A_187, B_185, C_186)!=A_187 | ~r1_tarski(k2_relat_1(C_186), B_185) | ~r1_tarski(k1_relat_1(C_186), A_187) | ~v1_relat_1(C_186))), inference(resolution, [status(thm)], [c_20, c_567])).
% 5.37/2.02  tff(c_1117, plain, (![C_197, A_198]: (k2_relat_1(C_197)=k1_xboole_0 | v1_funct_2(C_197, A_198, k2_relat_1(C_197)) | k1_relset_1(A_198, k2_relat_1(C_197), C_197)!=A_198 | ~r1_tarski(k1_relat_1(C_197), A_198) | ~v1_relat_1(C_197))), inference(resolution, [status(thm)], [c_80, c_1011])).
% 5.37/2.02  tff(c_1126, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1117, c_75])).
% 5.37/2.02  tff(c_1133, plain, (k2_relat_1('#skF_3')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_80, c_1126])).
% 5.37/2.02  tff(c_1134, plain, (k1_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_1133])).
% 5.37/2.02  tff(c_1137, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_732, c_1134])).
% 5.37/2.02  tff(c_1141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_1137])).
% 5.37/2.02  tff(c_1142, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1133])).
% 5.37/2.02  tff(c_557, plain, (![C_118, B_119, A_120]: (v1_xboole_0(C_118) | ~v1_xboole_0(B_119) | ~r1_tarski(k2_relat_1(C_118), B_119) | ~r1_tarski(k1_relat_1(C_118), A_120) | ~v1_relat_1(C_118))), inference(resolution, [status(thm)], [c_476, c_16])).
% 5.37/2.02  tff(c_562, plain, (![C_121, A_122]: (v1_xboole_0(C_121) | ~v1_xboole_0(k2_relat_1(C_121)) | ~r1_tarski(k1_relat_1(C_121), A_122) | ~v1_relat_1(C_121))), inference(resolution, [status(thm)], [c_80, c_557])).
% 5.37/2.02  tff(c_566, plain, (![C_121]: (v1_xboole_0(C_121) | ~v1_xboole_0(k2_relat_1(C_121)) | ~v1_relat_1(C_121))), inference(resolution, [status(thm)], [c_80, c_562])).
% 5.37/2.02  tff(c_1179, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1142, c_566])).
% 5.37/2.02  tff(c_1209, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6, c_1179])).
% 5.37/2.02  tff(c_1219, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1209, c_63])).
% 5.37/2.02  tff(c_87, plain, (![C_44, B_45, A_46]: (v1_xboole_0(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(B_45, A_46))) | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.37/2.02  tff(c_105, plain, (![B_50, A_51]: (v1_xboole_0(k2_zfmisc_1(B_50, A_51)) | ~v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_47, c_87])).
% 5.37/2.02  tff(c_110, plain, (![B_52, A_53]: (k2_zfmisc_1(B_52, A_53)=k1_xboole_0 | ~v1_xboole_0(A_53))), inference(resolution, [status(thm)], [c_105, c_63])).
% 5.37/2.02  tff(c_116, plain, (![B_52]: (k2_zfmisc_1(B_52, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_110])).
% 5.37/2.02  tff(c_226, plain, (![A_75, B_76]: (k1_relset_1(A_75, B_76, k2_zfmisc_1(A_75, B_76))=k1_relat_1(k2_zfmisc_1(A_75, B_76)))), inference(resolution, [status(thm)], [c_47, c_210])).
% 5.37/2.02  tff(c_354, plain, (![C_101, B_102]: (v1_funct_2(C_101, k1_xboole_0, B_102) | k1_relset_1(k1_xboole_0, B_102, C_101)!=k1_xboole_0 | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_102))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.37/2.02  tff(c_370, plain, (![B_102]: (v1_funct_2(k2_zfmisc_1(k1_xboole_0, B_102), k1_xboole_0, B_102) | k1_relset_1(k1_xboole_0, B_102, k2_zfmisc_1(k1_xboole_0, B_102))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_47, c_354])).
% 5.37/2.02  tff(c_374, plain, (![B_103]: (v1_funct_2(k2_zfmisc_1(k1_xboole_0, B_103), k1_xboole_0, B_103) | k1_relat_1(k2_zfmisc_1(k1_xboole_0, B_103))!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_226, c_370])).
% 5.37/2.02  tff(c_385, plain, (v1_funct_2(k1_xboole_0, k1_xboole_0, k1_xboole_0) | k1_relat_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_116, c_374])).
% 5.37/2.02  tff(c_390, plain, (v1_funct_2(k1_xboole_0, k1_xboole_0, k1_xboole_0) | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_116, c_385])).
% 5.37/2.02  tff(c_391, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_390])).
% 5.37/2.02  tff(c_1256, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1219, c_1219, c_391])).
% 5.37/2.02  tff(c_28, plain, (![A_29]: (v1_funct_2(k1_xboole_0, A_29, k1_xboole_0) | k1_xboole_0=A_29 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_29, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.37/2.02  tff(c_192, plain, (![A_29]: (v1_funct_2(k1_xboole_0, A_29, k1_xboole_0) | k1_xboole_0=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_47, c_116, c_28])).
% 5.37/2.02  tff(c_1376, plain, (![A_202]: (v1_funct_2('#skF_3', A_202, '#skF_3') | A_202='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1219, c_1219, c_1219, c_192])).
% 5.37/2.02  tff(c_1144, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1142, c_75])).
% 5.37/2.02  tff(c_1220, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1219, c_1144])).
% 5.37/2.02  tff(c_1382, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_1376, c_1220])).
% 5.37/2.02  tff(c_1388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1256, c_1382])).
% 5.37/2.02  tff(c_1389, plain, (v1_funct_2(k1_xboole_0, k1_xboole_0, k1_xboole_0)), inference(splitRight, [status(thm)], [c_390])).
% 5.37/2.02  tff(c_2780, plain, (v1_funct_2('#skF_3', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2745, c_2745, c_2745, c_1389])).
% 5.37/2.02  tff(c_1390, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_390])).
% 5.37/2.02  tff(c_2782, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2745, c_2745, c_1390])).
% 5.37/2.02  tff(c_2674, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2672, c_75])).
% 5.37/2.02  tff(c_2746, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2745, c_2674])).
% 5.37/2.02  tff(c_2924, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2780, c_2782, c_2746])).
% 5.37/2.02  tff(c_2925, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(splitRight, [status(thm)], [c_46])).
% 5.37/2.02  tff(c_3308, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3291, c_2925])).
% 5.37/2.02  tff(c_3325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_2931, c_2931, c_3308])).
% 5.37/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.37/2.02  
% 5.37/2.02  Inference rules
% 5.37/2.02  ----------------------
% 5.37/2.02  #Ref     : 0
% 5.37/2.02  #Sup     : 652
% 5.37/2.02  #Fact    : 0
% 5.37/2.02  #Define  : 0
% 5.37/2.02  #Split   : 7
% 5.37/2.02  #Chain   : 0
% 5.37/2.02  #Close   : 0
% 5.37/2.02  
% 5.37/2.02  Ordering : KBO
% 5.37/2.02  
% 5.37/2.02  Simplification rules
% 5.37/2.02  ----------------------
% 5.37/2.02  #Subsume      : 152
% 5.37/2.02  #Demod        : 925
% 5.37/2.02  #Tautology    : 247
% 5.37/2.02  #SimpNegUnit  : 17
% 5.37/2.02  #BackRed      : 183
% 5.37/2.02  
% 5.37/2.02  #Partial instantiations: 0
% 5.37/2.02  #Strategies tried      : 1
% 5.37/2.02  
% 5.37/2.02  Timing (in seconds)
% 5.37/2.02  ----------------------
% 5.37/2.03  Preprocessing        : 0.34
% 5.37/2.03  Parsing              : 0.18
% 5.37/2.03  CNF conversion       : 0.02
% 5.37/2.03  Main loop            : 0.91
% 5.37/2.03  Inferencing          : 0.32
% 5.37/2.03  Reduction            : 0.29
% 5.37/2.03  Demodulation         : 0.20
% 5.37/2.03  BG Simplification    : 0.04
% 5.37/2.03  Subsumption          : 0.20
% 5.37/2.03  Abstraction          : 0.05
% 5.37/2.03  MUC search           : 0.00
% 5.37/2.03  Cooper               : 0.00
% 5.37/2.03  Total                : 1.30
% 5.37/2.03  Index Insertion      : 0.00
% 5.37/2.03  Index Deletion       : 0.00
% 5.37/2.03  Index Matching       : 0.00
% 5.37/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
