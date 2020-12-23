%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:18 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   63 (  79 expanded)
%              Number of leaves         :   31 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :  110 ( 171 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r2_hidden > r1_relat_2 > m1_subset_1 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(r1_relat_2,type,(
    r1_relat_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_47,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v3_orders_2(A)
      <=> r1_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_orders_2)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_relat_2(A,B)
        <=> ! [C] :
              ( r2_hidden(C,B)
             => r2_hidden(k4_tarski(C,C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_2)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_38,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_30,plain,(
    ! [A_27] :
      ( l1_struct_0(A_27)
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_12,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_82,plain,(
    ! [A_49] :
      ( m1_subset_1(u1_orders_2(A_49),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_49),u1_struct_0(A_49))))
      | ~ l1_orders_2(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_10,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_85,plain,(
    ! [A_49] :
      ( v1_relat_1(u1_orders_2(A_49))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(A_49),u1_struct_0(A_49)))
      | ~ l1_orders_2(A_49) ) ),
    inference(resolution,[status(thm)],[c_82,c_10])).

tff(c_91,plain,(
    ! [A_49] :
      ( v1_relat_1(u1_orders_2(A_49))
      | ~ l1_orders_2(A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_85])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_47,plain,(
    ! [B_36,A_37] :
      ( v1_xboole_0(B_36)
      | ~ m1_subset_1(B_36,A_37)
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_55,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_47])).

tff(c_56,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_34,plain,(
    ~ r1_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_40,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_24,plain,(
    ! [A_19] :
      ( r1_relat_2(u1_orders_2(A_19),u1_struct_0(A_19))
      | ~ v3_orders_2(A_19)
      | ~ l1_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_105,plain,(
    ! [C_54,A_55,B_56] :
      ( r2_hidden(k4_tarski(C_54,C_54),A_55)
      | ~ r2_hidden(C_54,B_56)
      | ~ r1_relat_2(A_55,B_56)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_118,plain,(
    ! [B_59,A_60,A_61] :
      ( r2_hidden(k4_tarski(B_59,B_59),A_60)
      | ~ r1_relat_2(A_60,A_61)
      | ~ v1_relat_1(A_60)
      | ~ m1_subset_1(B_59,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_4,c_105])).

tff(c_169,plain,(
    ! [B_75,A_76] :
      ( r2_hidden(k4_tarski(B_75,B_75),u1_orders_2(A_76))
      | ~ v1_relat_1(u1_orders_2(A_76))
      | ~ m1_subset_1(B_75,u1_struct_0(A_76))
      | v1_xboole_0(u1_struct_0(A_76))
      | ~ v3_orders_2(A_76)
      | ~ l1_orders_2(A_76) ) ),
    inference(resolution,[status(thm)],[c_24,c_118])).

tff(c_26,plain,(
    ! [A_20,B_24,C_26] :
      ( r1_orders_2(A_20,B_24,C_26)
      | ~ r2_hidden(k4_tarski(B_24,C_26),u1_orders_2(A_20))
      | ~ m1_subset_1(C_26,u1_struct_0(A_20))
      | ~ m1_subset_1(B_24,u1_struct_0(A_20))
      | ~ l1_orders_2(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_186,plain,(
    ! [A_77,B_78] :
      ( r1_orders_2(A_77,B_78,B_78)
      | ~ v1_relat_1(u1_orders_2(A_77))
      | ~ m1_subset_1(B_78,u1_struct_0(A_77))
      | v1_xboole_0(u1_struct_0(A_77))
      | ~ v3_orders_2(A_77)
      | ~ l1_orders_2(A_77) ) ),
    inference(resolution,[status(thm)],[c_169,c_26])).

tff(c_194,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ v1_relat_1(u1_orders_2('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ v3_orders_2('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_186])).

tff(c_199,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ v1_relat_1(u1_orders_2('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_194])).

tff(c_200,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_34,c_199])).

tff(c_203,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_91,c_200])).

tff(c_207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_203])).

tff(c_209,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_20,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(u1_struct_0(A_18))
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_218,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_209,c_20])).

tff(c_221,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_218])).

tff(c_224,plain,(
    ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_221])).

tff(c_228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_224])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:45:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.26  
% 2.10/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.26  %$ r1_orders_2 > r2_hidden > r1_relat_2 > m1_subset_1 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.10/1.26  
% 2.10/1.26  %Foreground sorts:
% 2.10/1.26  
% 2.10/1.26  
% 2.10/1.26  %Background operators:
% 2.10/1.26  
% 2.10/1.26  
% 2.10/1.26  %Foreground operators:
% 2.10/1.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.10/1.26  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.10/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.10/1.26  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.10/1.26  tff(r1_relat_2, type, r1_relat_2: ($i * $i) > $o).
% 2.10/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.26  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.10/1.26  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.10/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.10/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.10/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.26  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.10/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.10/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.10/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.10/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.26  
% 2.10/1.28  tff(f_104, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 2.10/1.28  tff(f_87, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.10/1.28  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.10/1.28  tff(f_91, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 2.10/1.28  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.10/1.28  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.10/1.28  tff(f_71, axiom, (![A]: (l1_orders_2(A) => (v3_orders_2(A) <=> r1_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_orders_2)).
% 2.10/1.28  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_relat_2(A, B) <=> (![C]: (r2_hidden(C, B) => r2_hidden(k4_tarski(C, C), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_2)).
% 2.10/1.28  tff(f_83, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 2.10/1.28  tff(f_65, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.10/1.28  tff(c_38, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.10/1.28  tff(c_30, plain, (![A_27]: (l1_struct_0(A_27) | ~l1_orders_2(A_27))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.10/1.28  tff(c_42, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.10/1.28  tff(c_12, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.10/1.28  tff(c_82, plain, (![A_49]: (m1_subset_1(u1_orders_2(A_49), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_49), u1_struct_0(A_49)))) | ~l1_orders_2(A_49))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.10/1.28  tff(c_10, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.10/1.28  tff(c_85, plain, (![A_49]: (v1_relat_1(u1_orders_2(A_49)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(A_49), u1_struct_0(A_49))) | ~l1_orders_2(A_49))), inference(resolution, [status(thm)], [c_82, c_10])).
% 2.10/1.28  tff(c_91, plain, (![A_49]: (v1_relat_1(u1_orders_2(A_49)) | ~l1_orders_2(A_49))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_85])).
% 2.10/1.28  tff(c_36, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.10/1.28  tff(c_47, plain, (![B_36, A_37]: (v1_xboole_0(B_36) | ~m1_subset_1(B_36, A_37) | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.10/1.28  tff(c_55, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_47])).
% 2.10/1.28  tff(c_56, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_55])).
% 2.10/1.28  tff(c_34, plain, (~r1_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.10/1.28  tff(c_40, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.10/1.28  tff(c_24, plain, (![A_19]: (r1_relat_2(u1_orders_2(A_19), u1_struct_0(A_19)) | ~v3_orders_2(A_19) | ~l1_orders_2(A_19))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.10/1.28  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.10/1.28  tff(c_105, plain, (![C_54, A_55, B_56]: (r2_hidden(k4_tarski(C_54, C_54), A_55) | ~r2_hidden(C_54, B_56) | ~r1_relat_2(A_55, B_56) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.10/1.28  tff(c_118, plain, (![B_59, A_60, A_61]: (r2_hidden(k4_tarski(B_59, B_59), A_60) | ~r1_relat_2(A_60, A_61) | ~v1_relat_1(A_60) | ~m1_subset_1(B_59, A_61) | v1_xboole_0(A_61))), inference(resolution, [status(thm)], [c_4, c_105])).
% 2.10/1.28  tff(c_169, plain, (![B_75, A_76]: (r2_hidden(k4_tarski(B_75, B_75), u1_orders_2(A_76)) | ~v1_relat_1(u1_orders_2(A_76)) | ~m1_subset_1(B_75, u1_struct_0(A_76)) | v1_xboole_0(u1_struct_0(A_76)) | ~v3_orders_2(A_76) | ~l1_orders_2(A_76))), inference(resolution, [status(thm)], [c_24, c_118])).
% 2.10/1.28  tff(c_26, plain, (![A_20, B_24, C_26]: (r1_orders_2(A_20, B_24, C_26) | ~r2_hidden(k4_tarski(B_24, C_26), u1_orders_2(A_20)) | ~m1_subset_1(C_26, u1_struct_0(A_20)) | ~m1_subset_1(B_24, u1_struct_0(A_20)) | ~l1_orders_2(A_20))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.10/1.28  tff(c_186, plain, (![A_77, B_78]: (r1_orders_2(A_77, B_78, B_78) | ~v1_relat_1(u1_orders_2(A_77)) | ~m1_subset_1(B_78, u1_struct_0(A_77)) | v1_xboole_0(u1_struct_0(A_77)) | ~v3_orders_2(A_77) | ~l1_orders_2(A_77))), inference(resolution, [status(thm)], [c_169, c_26])).
% 2.10/1.28  tff(c_194, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | ~v1_relat_1(u1_orders_2('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2')) | ~v3_orders_2('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_36, c_186])).
% 2.10/1.28  tff(c_199, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | ~v1_relat_1(u1_orders_2('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_194])).
% 2.10/1.28  tff(c_200, plain, (~v1_relat_1(u1_orders_2('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_34, c_199])).
% 2.10/1.28  tff(c_203, plain, (~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_91, c_200])).
% 2.10/1.28  tff(c_207, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_203])).
% 2.10/1.28  tff(c_209, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_55])).
% 2.10/1.28  tff(c_20, plain, (![A_18]: (~v1_xboole_0(u1_struct_0(A_18)) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.10/1.28  tff(c_218, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_209, c_20])).
% 2.10/1.28  tff(c_221, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_42, c_218])).
% 2.10/1.28  tff(c_224, plain, (~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_30, c_221])).
% 2.10/1.28  tff(c_228, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_224])).
% 2.10/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.28  
% 2.10/1.28  Inference rules
% 2.10/1.28  ----------------------
% 2.10/1.28  #Ref     : 0
% 2.10/1.28  #Sup     : 35
% 2.10/1.28  #Fact    : 0
% 2.10/1.28  #Define  : 0
% 2.10/1.28  #Split   : 2
% 2.10/1.28  #Chain   : 0
% 2.10/1.28  #Close   : 0
% 2.10/1.28  
% 2.10/1.28  Ordering : KBO
% 2.10/1.28  
% 2.10/1.28  Simplification rules
% 2.10/1.28  ----------------------
% 2.10/1.28  #Subsume      : 0
% 2.10/1.28  #Demod        : 5
% 2.10/1.28  #Tautology    : 8
% 2.10/1.28  #SimpNegUnit  : 2
% 2.10/1.28  #BackRed      : 0
% 2.10/1.28  
% 2.10/1.28  #Partial instantiations: 0
% 2.10/1.28  #Strategies tried      : 1
% 2.10/1.28  
% 2.10/1.28  Timing (in seconds)
% 2.10/1.28  ----------------------
% 2.10/1.28  Preprocessing        : 0.30
% 2.10/1.28  Parsing              : 0.17
% 2.10/1.28  CNF conversion       : 0.02
% 2.10/1.28  Main loop            : 0.21
% 2.10/1.28  Inferencing          : 0.09
% 2.10/1.28  Reduction            : 0.05
% 2.10/1.28  Demodulation         : 0.04
% 2.10/1.28  BG Simplification    : 0.01
% 2.10/1.28  Subsumption          : 0.04
% 2.10/1.28  Abstraction          : 0.01
% 2.10/1.28  MUC search           : 0.00
% 2.10/1.28  Cooper               : 0.00
% 2.10/1.28  Total                : 0.54
% 2.10/1.28  Index Insertion      : 0.00
% 2.10/1.28  Index Deletion       : 0.00
% 2.10/1.28  Index Matching       : 0.00
% 2.10/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
