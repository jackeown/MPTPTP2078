%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:16 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 123 expanded)
%              Number of leaves         :   38 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  105 ( 241 expanded)
%              Number of equality atoms :   14 (  33 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_131,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_88,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_49,axiom,(
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

tff(f_69,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_543,plain,(
    ! [A_136,B_137,C_138] :
      ( k1_relset_1(A_136,B_137,C_138) = k1_relat_1(C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_567,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_543])).

tff(c_40,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_568,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_40])).

tff(c_26,plain,(
    ! [A_22,B_23] : v1_relat_1(k2_zfmisc_1(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_444,plain,(
    ! [B_116,A_117] :
      ( v1_relat_1(B_116)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(A_117))
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_455,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_444])).

tff(c_460,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_455])).

tff(c_480,plain,(
    ! [C_124,B_125,A_126] :
      ( v5_relat_1(C_124,B_125)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_126,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_504,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_480])).

tff(c_22,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k2_relat_1(B_20),A_19)
      | ~ v5_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_423,plain,(
    ! [A_110,B_111] :
      ( r2_hidden('#skF_2'(A_110,B_111),B_111)
      | r1_xboole_0(A_110,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,B_15)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_434,plain,(
    ! [A_110,B_111] :
      ( m1_subset_1('#skF_2'(A_110,B_111),B_111)
      | r1_xboole_0(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_423,c_16])).

tff(c_583,plain,(
    ! [A_146,B_147,C_148] :
      ( k2_relset_1(A_146,B_147,C_148) = k2_relat_1(C_148)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_607,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_583])).

tff(c_403,plain,(
    ! [A_104,B_105] :
      ( r2_hidden('#skF_2'(A_104,B_105),A_104)
      | r1_xboole_0(A_104,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_38,plain,(
    ! [D_45] :
      ( ~ r2_hidden(D_45,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1(D_45,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_415,plain,(
    ! [B_105] :
      ( ~ m1_subset_1('#skF_2'(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_105),'#skF_5')
      | r1_xboole_0(k2_relset_1('#skF_4','#skF_5','#skF_6'),B_105) ) ),
    inference(resolution,[status(thm)],[c_403,c_38])).

tff(c_675,plain,(
    ! [B_152] :
      ( ~ m1_subset_1('#skF_2'(k2_relat_1('#skF_6'),B_152),'#skF_5')
      | r1_xboole_0(k2_relat_1('#skF_6'),B_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_607,c_607,c_415])).

tff(c_680,plain,(
    r1_xboole_0(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_434,c_675])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( ~ r1_xboole_0(B_13,A_12)
      | ~ r1_tarski(B_13,A_12)
      | v1_xboole_0(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_687,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_680,c_14])).

tff(c_688,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_687])).

tff(c_691,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_688])).

tff(c_695,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_504,c_691])).

tff(c_696,plain,(
    v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_687])).

tff(c_28,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(k2_relat_1(A_24))
      | ~ v1_relat_1(A_24)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_700,plain,
    ( ~ v1_relat_1('#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_696,c_28])).

tff(c_709,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_700])).

tff(c_24,plain,(
    ! [A_21] :
      ( v1_xboole_0(k1_relat_1(A_21))
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_50,plain,(
    ! [A_51] :
      ( r2_hidden('#skF_3'(A_51),A_51)
      | k1_xboole_0 = A_51 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_55,plain,(
    ! [A_52] :
      ( ~ v1_xboole_0(A_52)
      | k1_xboole_0 = A_52 ) ),
    inference(resolution,[status(thm)],[c_50,c_2])).

tff(c_59,plain,(
    ! [A_21] :
      ( k1_relat_1(A_21) = k1_xboole_0
      | ~ v1_xboole_0(A_21) ) ),
    inference(resolution,[status(thm)],[c_24,c_55])).

tff(c_714,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_709,c_59])).

tff(c_721,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_568,c_714])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:02:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.38  
% 2.69/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.38  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2
% 2.69/1.38  
% 2.69/1.38  %Foreground sorts:
% 2.69/1.38  
% 2.69/1.38  
% 2.69/1.38  %Background operators:
% 2.69/1.38  
% 2.69/1.38  
% 2.69/1.38  %Foreground operators:
% 2.69/1.38  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.69/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.69/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.69/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.69/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.69/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.69/1.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.69/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.69/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.69/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.69/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.69/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.38  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.69/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.69/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.69/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.69/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.69/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.38  
% 2.90/1.40  tff(f_131, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 2.90/1.40  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.90/1.40  tff(f_88, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.90/1.40  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.90/1.40  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.90/1.40  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.90/1.40  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.90/1.40  tff(f_69, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.90/1.40  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.90/1.40  tff(f_65, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.90/1.40  tff(f_96, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.90/1.40  tff(f_86, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 2.90/1.40  tff(f_57, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.90/1.40  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.90/1.40  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.90/1.40  tff(c_543, plain, (![A_136, B_137, C_138]: (k1_relset_1(A_136, B_137, C_138)=k1_relat_1(C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.90/1.40  tff(c_567, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_543])).
% 2.90/1.40  tff(c_40, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.90/1.40  tff(c_568, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_567, c_40])).
% 2.90/1.40  tff(c_26, plain, (![A_22, B_23]: (v1_relat_1(k2_zfmisc_1(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.90/1.40  tff(c_444, plain, (![B_116, A_117]: (v1_relat_1(B_116) | ~m1_subset_1(B_116, k1_zfmisc_1(A_117)) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.90/1.40  tff(c_455, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_42, c_444])).
% 2.90/1.40  tff(c_460, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_455])).
% 2.90/1.40  tff(c_480, plain, (![C_124, B_125, A_126]: (v5_relat_1(C_124, B_125) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.90/1.40  tff(c_504, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_480])).
% 2.90/1.40  tff(c_22, plain, (![B_20, A_19]: (r1_tarski(k2_relat_1(B_20), A_19) | ~v5_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.90/1.40  tff(c_423, plain, (![A_110, B_111]: (r2_hidden('#skF_2'(A_110, B_111), B_111) | r1_xboole_0(A_110, B_111))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.90/1.40  tff(c_16, plain, (![A_14, B_15]: (m1_subset_1(A_14, B_15) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.90/1.40  tff(c_434, plain, (![A_110, B_111]: (m1_subset_1('#skF_2'(A_110, B_111), B_111) | r1_xboole_0(A_110, B_111))), inference(resolution, [status(thm)], [c_423, c_16])).
% 2.90/1.40  tff(c_583, plain, (![A_146, B_147, C_148]: (k2_relset_1(A_146, B_147, C_148)=k2_relat_1(C_148) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.90/1.40  tff(c_607, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_583])).
% 2.90/1.40  tff(c_403, plain, (![A_104, B_105]: (r2_hidden('#skF_2'(A_104, B_105), A_104) | r1_xboole_0(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.90/1.40  tff(c_38, plain, (![D_45]: (~r2_hidden(D_45, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1(D_45, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.90/1.40  tff(c_415, plain, (![B_105]: (~m1_subset_1('#skF_2'(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_105), '#skF_5') | r1_xboole_0(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), B_105))), inference(resolution, [status(thm)], [c_403, c_38])).
% 2.90/1.40  tff(c_675, plain, (![B_152]: (~m1_subset_1('#skF_2'(k2_relat_1('#skF_6'), B_152), '#skF_5') | r1_xboole_0(k2_relat_1('#skF_6'), B_152))), inference(demodulation, [status(thm), theory('equality')], [c_607, c_607, c_415])).
% 2.90/1.40  tff(c_680, plain, (r1_xboole_0(k2_relat_1('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_434, c_675])).
% 2.90/1.40  tff(c_14, plain, (![B_13, A_12]: (~r1_xboole_0(B_13, A_12) | ~r1_tarski(B_13, A_12) | v1_xboole_0(B_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.90/1.40  tff(c_687, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | v1_xboole_0(k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_680, c_14])).
% 2.90/1.40  tff(c_688, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_687])).
% 2.90/1.40  tff(c_691, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_22, c_688])).
% 2.90/1.40  tff(c_695, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_460, c_504, c_691])).
% 2.90/1.40  tff(c_696, plain, (v1_xboole_0(k2_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_687])).
% 2.90/1.40  tff(c_28, plain, (![A_24]: (~v1_xboole_0(k2_relat_1(A_24)) | ~v1_relat_1(A_24) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.90/1.40  tff(c_700, plain, (~v1_relat_1('#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_696, c_28])).
% 2.90/1.40  tff(c_709, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_460, c_700])).
% 2.90/1.40  tff(c_24, plain, (![A_21]: (v1_xboole_0(k1_relat_1(A_21)) | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.90/1.40  tff(c_50, plain, (![A_51]: (r2_hidden('#skF_3'(A_51), A_51) | k1_xboole_0=A_51)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.90/1.40  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.90/1.40  tff(c_55, plain, (![A_52]: (~v1_xboole_0(A_52) | k1_xboole_0=A_52)), inference(resolution, [status(thm)], [c_50, c_2])).
% 2.90/1.40  tff(c_59, plain, (![A_21]: (k1_relat_1(A_21)=k1_xboole_0 | ~v1_xboole_0(A_21))), inference(resolution, [status(thm)], [c_24, c_55])).
% 2.90/1.40  tff(c_714, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_709, c_59])).
% 2.90/1.40  tff(c_721, plain, $false, inference(negUnitSimplification, [status(thm)], [c_568, c_714])).
% 2.90/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.40  
% 2.90/1.40  Inference rules
% 2.90/1.40  ----------------------
% 2.90/1.40  #Ref     : 0
% 2.90/1.40  #Sup     : 131
% 2.90/1.40  #Fact    : 0
% 2.90/1.40  #Define  : 0
% 2.90/1.40  #Split   : 7
% 2.90/1.40  #Chain   : 0
% 2.90/1.40  #Close   : 0
% 2.90/1.40  
% 2.90/1.40  Ordering : KBO
% 2.90/1.40  
% 2.90/1.40  Simplification rules
% 2.90/1.40  ----------------------
% 2.90/1.40  #Subsume      : 20
% 2.90/1.40  #Demod        : 35
% 2.90/1.40  #Tautology    : 20
% 2.90/1.40  #SimpNegUnit  : 7
% 2.90/1.40  #BackRed      : 16
% 2.90/1.40  
% 2.90/1.40  #Partial instantiations: 0
% 2.90/1.40  #Strategies tried      : 1
% 2.90/1.40  
% 2.90/1.40  Timing (in seconds)
% 2.90/1.40  ----------------------
% 2.90/1.40  Preprocessing        : 0.31
% 2.90/1.40  Parsing              : 0.17
% 2.90/1.40  CNF conversion       : 0.02
% 2.90/1.40  Main loop            : 0.32
% 2.90/1.40  Inferencing          : 0.13
% 2.90/1.40  Reduction            : 0.09
% 2.90/1.40  Demodulation         : 0.05
% 2.90/1.40  BG Simplification    : 0.02
% 2.90/1.40  Subsumption          : 0.05
% 2.90/1.40  Abstraction          : 0.02
% 2.90/1.40  MUC search           : 0.00
% 2.90/1.40  Cooper               : 0.00
% 2.90/1.40  Total                : 0.66
% 2.90/1.40  Index Insertion      : 0.00
% 2.90/1.40  Index Deletion       : 0.00
% 2.90/1.40  Index Matching       : 0.00
% 2.90/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
