%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:28 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 172 expanded)
%              Number of leaves         :   39 (  77 expanded)
%              Depth                    :   13
%              Number of atoms          :  129 ( 418 expanded)
%              Number of equality atoms :   30 ( 130 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

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

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
      <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

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

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_61,axiom,(
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

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1111,plain,(
    ! [A_224,B_225,C_226,D_227] :
      ( k7_relset_1(A_224,B_225,C_226,D_227) = k9_relat_1(C_226,D_227)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(A_224,B_225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1122,plain,(
    ! [D_227] : k7_relset_1('#skF_4','#skF_5','#skF_6',D_227) = k9_relat_1('#skF_6',D_227) ),
    inference(resolution,[status(thm)],[c_44,c_1111])).

tff(c_1249,plain,(
    ! [A_259,B_260,C_261] :
      ( k7_relset_1(A_259,B_260,C_261,A_259) = k2_relset_1(A_259,B_260,C_261)
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(A_259,B_260))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1257,plain,(
    k7_relset_1('#skF_4','#skF_5','#skF_6','#skF_4') = k2_relset_1('#skF_4','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_1249])).

tff(c_1261,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k9_relat_1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1122,c_1257])).

tff(c_42,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1279,plain,(
    k9_relat_1('#skF_6','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1261,c_42])).

tff(c_1262,plain,(
    ! [A_262,B_263,C_264] :
      ( r2_hidden('#skF_2'(A_262,B_263,C_264),B_263)
      | k2_relset_1(A_262,B_263,C_264) = B_263
      | ~ m1_subset_1(C_264,k1_zfmisc_1(k2_zfmisc_1(A_262,B_263))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1270,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_6'),'#skF_5')
    | k2_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_44,c_1262])).

tff(c_1275,plain,(
    r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1270])).

tff(c_16,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_103,plain,(
    ! [B_62,A_63] :
      ( v1_relat_1(B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63))
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_109,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_103])).

tff(c_113,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_109])).

tff(c_52,plain,(
    ! [D_47] :
      ( r2_hidden('#skF_7'(D_47),'#skF_4')
      | ~ r2_hidden(D_47,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_50,plain,(
    ! [D_47] :
      ( k1_funct_1('#skF_6','#skF_7'(D_47)) = D_47
      | ~ r2_hidden(D_47,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_48,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_46,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1580,plain,(
    ! [D_307,C_308,A_309,B_310] :
      ( r2_hidden(k1_funct_1(D_307,C_308),k2_relset_1(A_309,B_310,D_307))
      | k1_xboole_0 = B_310
      | ~ r2_hidden(C_308,A_309)
      | ~ m1_subset_1(D_307,k1_zfmisc_1(k2_zfmisc_1(A_309,B_310)))
      | ~ v1_funct_2(D_307,A_309,B_310)
      | ~ v1_funct_1(D_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1594,plain,(
    ! [C_308] :
      ( r2_hidden(k1_funct_1('#skF_6',C_308),k9_relat_1('#skF_6','#skF_4'))
      | k1_xboole_0 = '#skF_5'
      | ~ r2_hidden(C_308,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1261,c_1580])).

tff(c_1606,plain,(
    ! [C_308] :
      ( r2_hidden(k1_funct_1('#skF_6',C_308),k9_relat_1('#skF_6','#skF_4'))
      | k1_xboole_0 = '#skF_5'
      | ~ r2_hidden(C_308,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_1594])).

tff(c_1610,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1606])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1624,plain,(
    ! [A_3] : r1_tarski('#skF_5',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1610,c_8])).

tff(c_139,plain,(
    ! [A_69,B_70,C_71] :
      ( m1_subset_1(k2_relset_1(A_69,B_70,C_71),k1_zfmisc_1(B_70))
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_149,plain,(
    ! [A_75,B_76,C_77] :
      ( r1_tarski(k2_relset_1(A_75,B_76,C_77),B_76)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(resolution,[status(thm)],[c_139,c_10])).

tff(c_160,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_149])).

tff(c_1278,plain,(
    r1_tarski(k9_relat_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1261,c_160])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1298,plain,
    ( k9_relat_1('#skF_6','#skF_4') = '#skF_5'
    | ~ r1_tarski('#skF_5',k9_relat_1('#skF_6','#skF_4')) ),
    inference(resolution,[status(thm)],[c_1278,c_2])).

tff(c_1304,plain,(
    ~ r1_tarski('#skF_5',k9_relat_1('#skF_6','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_1279,c_1298])).

tff(c_1632,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1624,c_1304])).

tff(c_1635,plain,(
    ! [C_311] :
      ( r2_hidden(k1_funct_1('#skF_6',C_311),k9_relat_1('#skF_6','#skF_4'))
      | ~ r2_hidden(C_311,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_1606])).

tff(c_1648,plain,(
    ! [D_315] :
      ( r2_hidden(D_315,k9_relat_1('#skF_6','#skF_4'))
      | ~ r2_hidden('#skF_7'(D_315),'#skF_4')
      | ~ r2_hidden(D_315,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1635])).

tff(c_1652,plain,(
    ! [D_47] :
      ( r2_hidden(D_47,k9_relat_1('#skF_6','#skF_4'))
      | ~ r2_hidden(D_47,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_52,c_1648])).

tff(c_22,plain,(
    ! [A_11,B_12,C_13] :
      ( r2_hidden(k4_tarski('#skF_1'(A_11,B_12,C_13),A_11),C_13)
      | ~ r2_hidden(A_11,k9_relat_1(C_13,B_12))
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1406,plain,(
    ! [E_280,A_281,B_282,C_283] :
      ( ~ r2_hidden(k4_tarski(E_280,'#skF_2'(A_281,B_282,C_283)),C_283)
      | k2_relset_1(A_281,B_282,C_283) = B_282
      | ~ m1_subset_1(C_283,k1_zfmisc_1(k2_zfmisc_1(A_281,B_282))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1773,plain,(
    ! [A_330,B_331,C_332,B_333] :
      ( k2_relset_1(A_330,B_331,C_332) = B_331
      | ~ m1_subset_1(C_332,k1_zfmisc_1(k2_zfmisc_1(A_330,B_331)))
      | ~ r2_hidden('#skF_2'(A_330,B_331,C_332),k9_relat_1(C_332,B_333))
      | ~ v1_relat_1(C_332) ) ),
    inference(resolution,[status(thm)],[c_22,c_1406])).

tff(c_1777,plain,(
    ! [A_330,B_331] :
      ( k2_relset_1(A_330,B_331,'#skF_6') = B_331
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_330,B_331)))
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden('#skF_2'(A_330,B_331,'#skF_6'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1652,c_1773])).

tff(c_1845,plain,(
    ! [A_342,B_343] :
      ( k2_relset_1(A_342,B_343,'#skF_6') = B_343
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_342,B_343)))
      | ~ r2_hidden('#skF_2'(A_342,B_343,'#skF_6'),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_1777])).

tff(c_1851,plain,
    ( k2_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_5'
    | ~ r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_1845])).

tff(c_1855,plain,(
    k9_relat_1('#skF_6','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1275,c_1261,c_1851])).

tff(c_1857,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1279,c_1855])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.88/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.68  
% 3.88/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.68  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 3.88/1.68  
% 3.88/1.68  %Foreground sorts:
% 3.88/1.68  
% 3.88/1.68  
% 3.88/1.68  %Background operators:
% 3.88/1.68  
% 3.88/1.68  
% 3.88/1.68  %Foreground operators:
% 3.88/1.68  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.88/1.68  tff('#skF_7', type, '#skF_7': $i > $i).
% 3.88/1.68  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.88/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.88/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.88/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.88/1.68  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.88/1.68  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.88/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.88/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.88/1.68  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.88/1.68  tff('#skF_5', type, '#skF_5': $i).
% 3.88/1.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.88/1.68  tff('#skF_6', type, '#skF_6': $i).
% 3.88/1.68  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.88/1.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.88/1.68  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.88/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.88/1.68  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.88/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.88/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.88/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.88/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.88/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.88/1.68  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.88/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.88/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.88/1.68  
% 3.88/1.70  tff(f_114, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 3.88/1.70  tff(f_65, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.88/1.70  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 3.88/1.70  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relset_1)).
% 3.88/1.70  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.88/1.70  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.88/1.70  tff(f_95, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 3.88/1.70  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.88/1.70  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.88/1.70  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.88/1.70  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.88/1.70  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 3.88/1.70  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.88/1.70  tff(c_1111, plain, (![A_224, B_225, C_226, D_227]: (k7_relset_1(A_224, B_225, C_226, D_227)=k9_relat_1(C_226, D_227) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(A_224, B_225))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.88/1.70  tff(c_1122, plain, (![D_227]: (k7_relset_1('#skF_4', '#skF_5', '#skF_6', D_227)=k9_relat_1('#skF_6', D_227))), inference(resolution, [status(thm)], [c_44, c_1111])).
% 3.88/1.70  tff(c_1249, plain, (![A_259, B_260, C_261]: (k7_relset_1(A_259, B_260, C_261, A_259)=k2_relset_1(A_259, B_260, C_261) | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1(A_259, B_260))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.88/1.70  tff(c_1257, plain, (k7_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_4')=k2_relset_1('#skF_4', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_44, c_1249])).
% 3.88/1.70  tff(c_1261, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k9_relat_1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1122, c_1257])).
% 3.88/1.70  tff(c_42, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.88/1.70  tff(c_1279, plain, (k9_relat_1('#skF_6', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1261, c_42])).
% 3.88/1.70  tff(c_1262, plain, (![A_262, B_263, C_264]: (r2_hidden('#skF_2'(A_262, B_263, C_264), B_263) | k2_relset_1(A_262, B_263, C_264)=B_263 | ~m1_subset_1(C_264, k1_zfmisc_1(k2_zfmisc_1(A_262, B_263))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.88/1.70  tff(c_1270, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_6'), '#skF_5') | k2_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_44, c_1262])).
% 3.88/1.70  tff(c_1275, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_1270])).
% 3.88/1.70  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.88/1.70  tff(c_103, plain, (![B_62, A_63]: (v1_relat_1(B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.88/1.70  tff(c_109, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_103])).
% 3.88/1.70  tff(c_113, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_109])).
% 3.88/1.70  tff(c_52, plain, (![D_47]: (r2_hidden('#skF_7'(D_47), '#skF_4') | ~r2_hidden(D_47, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.88/1.70  tff(c_50, plain, (![D_47]: (k1_funct_1('#skF_6', '#skF_7'(D_47))=D_47 | ~r2_hidden(D_47, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.88/1.70  tff(c_48, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.88/1.70  tff(c_46, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.88/1.70  tff(c_1580, plain, (![D_307, C_308, A_309, B_310]: (r2_hidden(k1_funct_1(D_307, C_308), k2_relset_1(A_309, B_310, D_307)) | k1_xboole_0=B_310 | ~r2_hidden(C_308, A_309) | ~m1_subset_1(D_307, k1_zfmisc_1(k2_zfmisc_1(A_309, B_310))) | ~v1_funct_2(D_307, A_309, B_310) | ~v1_funct_1(D_307))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.88/1.70  tff(c_1594, plain, (![C_308]: (r2_hidden(k1_funct_1('#skF_6', C_308), k9_relat_1('#skF_6', '#skF_4')) | k1_xboole_0='#skF_5' | ~r2_hidden(C_308, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1261, c_1580])).
% 3.88/1.70  tff(c_1606, plain, (![C_308]: (r2_hidden(k1_funct_1('#skF_6', C_308), k9_relat_1('#skF_6', '#skF_4')) | k1_xboole_0='#skF_5' | ~r2_hidden(C_308, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_1594])).
% 3.88/1.70  tff(c_1610, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_1606])).
% 3.88/1.70  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.88/1.70  tff(c_1624, plain, (![A_3]: (r1_tarski('#skF_5', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1610, c_8])).
% 3.88/1.70  tff(c_139, plain, (![A_69, B_70, C_71]: (m1_subset_1(k2_relset_1(A_69, B_70, C_71), k1_zfmisc_1(B_70)) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.88/1.70  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.88/1.70  tff(c_149, plain, (![A_75, B_76, C_77]: (r1_tarski(k2_relset_1(A_75, B_76, C_77), B_76) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(resolution, [status(thm)], [c_139, c_10])).
% 3.88/1.70  tff(c_160, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_44, c_149])).
% 3.88/1.70  tff(c_1278, plain, (r1_tarski(k9_relat_1('#skF_6', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1261, c_160])).
% 3.88/1.70  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.88/1.70  tff(c_1298, plain, (k9_relat_1('#skF_6', '#skF_4')='#skF_5' | ~r1_tarski('#skF_5', k9_relat_1('#skF_6', '#skF_4'))), inference(resolution, [status(thm)], [c_1278, c_2])).
% 3.88/1.70  tff(c_1304, plain, (~r1_tarski('#skF_5', k9_relat_1('#skF_6', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1279, c_1298])).
% 3.88/1.70  tff(c_1632, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1624, c_1304])).
% 3.88/1.70  tff(c_1635, plain, (![C_311]: (r2_hidden(k1_funct_1('#skF_6', C_311), k9_relat_1('#skF_6', '#skF_4')) | ~r2_hidden(C_311, '#skF_4'))), inference(splitRight, [status(thm)], [c_1606])).
% 3.88/1.70  tff(c_1648, plain, (![D_315]: (r2_hidden(D_315, k9_relat_1('#skF_6', '#skF_4')) | ~r2_hidden('#skF_7'(D_315), '#skF_4') | ~r2_hidden(D_315, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_1635])).
% 3.88/1.70  tff(c_1652, plain, (![D_47]: (r2_hidden(D_47, k9_relat_1('#skF_6', '#skF_4')) | ~r2_hidden(D_47, '#skF_5'))), inference(resolution, [status(thm)], [c_52, c_1648])).
% 3.88/1.70  tff(c_22, plain, (![A_11, B_12, C_13]: (r2_hidden(k4_tarski('#skF_1'(A_11, B_12, C_13), A_11), C_13) | ~r2_hidden(A_11, k9_relat_1(C_13, B_12)) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.88/1.70  tff(c_1406, plain, (![E_280, A_281, B_282, C_283]: (~r2_hidden(k4_tarski(E_280, '#skF_2'(A_281, B_282, C_283)), C_283) | k2_relset_1(A_281, B_282, C_283)=B_282 | ~m1_subset_1(C_283, k1_zfmisc_1(k2_zfmisc_1(A_281, B_282))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.88/1.70  tff(c_1773, plain, (![A_330, B_331, C_332, B_333]: (k2_relset_1(A_330, B_331, C_332)=B_331 | ~m1_subset_1(C_332, k1_zfmisc_1(k2_zfmisc_1(A_330, B_331))) | ~r2_hidden('#skF_2'(A_330, B_331, C_332), k9_relat_1(C_332, B_333)) | ~v1_relat_1(C_332))), inference(resolution, [status(thm)], [c_22, c_1406])).
% 3.88/1.70  tff(c_1777, plain, (![A_330, B_331]: (k2_relset_1(A_330, B_331, '#skF_6')=B_331 | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_330, B_331))) | ~v1_relat_1('#skF_6') | ~r2_hidden('#skF_2'(A_330, B_331, '#skF_6'), '#skF_5'))), inference(resolution, [status(thm)], [c_1652, c_1773])).
% 3.88/1.70  tff(c_1845, plain, (![A_342, B_343]: (k2_relset_1(A_342, B_343, '#skF_6')=B_343 | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_342, B_343))) | ~r2_hidden('#skF_2'(A_342, B_343, '#skF_6'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_1777])).
% 3.88/1.70  tff(c_1851, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_5' | ~r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_44, c_1845])).
% 3.88/1.70  tff(c_1855, plain, (k9_relat_1('#skF_6', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1275, c_1261, c_1851])).
% 3.88/1.70  tff(c_1857, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1279, c_1855])).
% 3.88/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.70  
% 3.88/1.70  Inference rules
% 3.88/1.70  ----------------------
% 3.88/1.70  #Ref     : 0
% 3.88/1.70  #Sup     : 375
% 3.88/1.70  #Fact    : 0
% 3.88/1.70  #Define  : 0
% 3.88/1.70  #Split   : 10
% 3.88/1.70  #Chain   : 0
% 3.88/1.70  #Close   : 0
% 3.88/1.70  
% 3.88/1.70  Ordering : KBO
% 3.88/1.70  
% 3.88/1.70  Simplification rules
% 3.88/1.70  ----------------------
% 3.88/1.70  #Subsume      : 27
% 3.88/1.70  #Demod        : 297
% 3.88/1.70  #Tautology    : 174
% 3.88/1.70  #SimpNegUnit  : 14
% 3.88/1.70  #BackRed      : 47
% 3.88/1.70  
% 3.88/1.70  #Partial instantiations: 0
% 3.88/1.70  #Strategies tried      : 1
% 3.88/1.70  
% 3.88/1.70  Timing (in seconds)
% 3.88/1.70  ----------------------
% 3.88/1.70  Preprocessing        : 0.32
% 3.88/1.70  Parsing              : 0.16
% 3.88/1.70  CNF conversion       : 0.02
% 3.88/1.70  Main loop            : 0.56
% 3.88/1.70  Inferencing          : 0.21
% 3.88/1.70  Reduction            : 0.18
% 3.88/1.70  Demodulation         : 0.13
% 3.88/1.70  BG Simplification    : 0.03
% 3.88/1.70  Subsumption          : 0.09
% 3.88/1.70  Abstraction          : 0.03
% 3.88/1.70  MUC search           : 0.00
% 3.88/1.70  Cooper               : 0.00
% 3.88/1.70  Total                : 0.91
% 3.88/1.70  Index Insertion      : 0.00
% 3.88/1.70  Index Deletion       : 0.00
% 3.88/1.70  Index Matching       : 0.00
% 3.88/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
