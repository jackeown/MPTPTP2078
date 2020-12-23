%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:18 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 104 expanded)
%              Number of leaves         :   35 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  126 ( 245 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r2_hidden > r1_relat_2 > m1_subset_1 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_relat_2,type,(
    r1_relat_2: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v3_orders_2(A)
      <=> r1_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_orders_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_relat_2(A,B)
        <=> ! [C] :
              ( r2_hidden(C,B)
             => r2_hidden(k4_tarski(C,C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_38,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_30,plain,(
    ! [A_46] :
      ( l1_struct_0(A_46)
      | ~ l1_orders_2(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_12,plain,(
    ! [A_25,B_26] : v1_relat_1(k2_zfmisc_1(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_32,plain,(
    ! [A_47] :
      ( m1_subset_1(u1_orders_2(A_47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_47),u1_struct_0(A_47))))
      | ~ l1_orders_2(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_10,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_1'(A_7),A_7)
      | v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_55,plain,(
    ! [C_61,A_62,B_63] :
      ( r2_hidden(C_61,A_62)
      | ~ r2_hidden(C_61,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_61,plain,(
    ! [A_7,A_62] :
      ( r2_hidden('#skF_1'(A_7),A_62)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(A_62))
      | v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_55])).

tff(c_75,plain,(
    ! [A_72,B_73] :
      ( k4_tarski('#skF_2'(A_72,B_73),'#skF_3'(A_72,B_73)) = B_73
      | ~ r2_hidden(B_73,A_72)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [C_20,D_21,A_7] :
      ( k4_tarski(C_20,D_21) != '#skF_1'(A_7)
      | v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_79,plain,(
    ! [B_73,A_7,A_72] :
      ( B_73 != '#skF_1'(A_7)
      | v1_relat_1(A_7)
      | ~ r2_hidden(B_73,A_72)
      | ~ v1_relat_1(A_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_8])).

tff(c_103,plain,(
    ! [A_80,A_81] :
      ( v1_relat_1(A_80)
      | ~ r2_hidden('#skF_1'(A_80),A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_79])).

tff(c_117,plain,(
    ! [A_82,A_83] :
      ( ~ v1_relat_1(A_82)
      | ~ m1_subset_1(A_83,k1_zfmisc_1(A_82))
      | v1_relat_1(A_83) ) ),
    inference(resolution,[status(thm)],[c_61,c_103])).

tff(c_120,plain,(
    ! [A_47] :
      ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(A_47),u1_struct_0(A_47)))
      | v1_relat_1(u1_orders_2(A_47))
      | ~ l1_orders_2(A_47) ) ),
    inference(resolution,[status(thm)],[c_32,c_117])).

tff(c_123,plain,(
    ! [A_47] :
      ( v1_relat_1(u1_orders_2(A_47))
      | ~ l1_orders_2(A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_120])).

tff(c_34,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_40,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_24,plain,(
    ! [A_38] :
      ( r1_relat_2(u1_orders_2(A_38),u1_struct_0(A_38))
      | ~ v3_orders_2(A_38)
      | ~ l1_orders_2(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_85,plain,(
    ! [C_74,A_75,B_76] :
      ( r2_hidden(k4_tarski(C_74,C_74),A_75)
      | ~ r2_hidden(C_74,B_76)
      | ~ r1_relat_2(A_75,B_76)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_165,plain,(
    ! [A_100,A_101,B_102] :
      ( r2_hidden(k4_tarski(A_100,A_100),A_101)
      | ~ r1_relat_2(A_101,B_102)
      | ~ v1_relat_1(A_101)
      | v1_xboole_0(B_102)
      | ~ m1_subset_1(A_100,B_102) ) ),
    inference(resolution,[status(thm)],[c_4,c_85])).

tff(c_252,plain,(
    ! [A_129,A_130] :
      ( r2_hidden(k4_tarski(A_129,A_129),u1_orders_2(A_130))
      | ~ v1_relat_1(u1_orders_2(A_130))
      | v1_xboole_0(u1_struct_0(A_130))
      | ~ m1_subset_1(A_129,u1_struct_0(A_130))
      | ~ v3_orders_2(A_130)
      | ~ l1_orders_2(A_130) ) ),
    inference(resolution,[status(thm)],[c_24,c_165])).

tff(c_26,plain,(
    ! [A_39,B_43,C_45] :
      ( r1_orders_2(A_39,B_43,C_45)
      | ~ r2_hidden(k4_tarski(B_43,C_45),u1_orders_2(A_39))
      | ~ m1_subset_1(C_45,u1_struct_0(A_39))
      | ~ m1_subset_1(B_43,u1_struct_0(A_39))
      | ~ l1_orders_2(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_268,plain,(
    ! [A_131,A_132] :
      ( r1_orders_2(A_131,A_132,A_132)
      | ~ v1_relat_1(u1_orders_2(A_131))
      | v1_xboole_0(u1_struct_0(A_131))
      | ~ m1_subset_1(A_132,u1_struct_0(A_131))
      | ~ v3_orders_2(A_131)
      | ~ l1_orders_2(A_131) ) ),
    inference(resolution,[status(thm)],[c_252,c_26])).

tff(c_270,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_6')
    | ~ v1_relat_1(u1_orders_2('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ v3_orders_2('#skF_5')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_268])).

tff(c_273,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_6')
    | ~ v1_relat_1(u1_orders_2('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40,c_270])).

tff(c_274,plain,
    ( ~ v1_relat_1(u1_orders_2('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_273])).

tff(c_275,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_274])).

tff(c_278,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_123,c_275])).

tff(c_282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_278])).

tff(c_283,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_274])).

tff(c_20,plain,(
    ! [A_37] :
      ( ~ v1_xboole_0(u1_struct_0(A_37))
      | ~ l1_struct_0(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_291,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_283,c_20])).

tff(c_294,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_291])).

tff(c_297,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_294])).

tff(c_301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_297])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:02:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.33  
% 2.54/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.33  %$ r1_orders_2 > r2_hidden > r1_relat_2 > m1_subset_1 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 2.54/1.33  
% 2.54/1.33  %Foreground sorts:
% 2.54/1.33  
% 2.54/1.33  
% 2.54/1.33  %Background operators:
% 2.54/1.33  
% 2.54/1.33  
% 2.54/1.33  %Foreground operators:
% 2.54/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.54/1.33  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.54/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.54/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.54/1.33  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.54/1.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.54/1.33  tff(r1_relat_2, type, r1_relat_2: ($i * $i) > $o).
% 2.54/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.54/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.54/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.54/1.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.54/1.33  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.54/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.54/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.54/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.54/1.33  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.54/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.54/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.54/1.33  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.54/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.54/1.33  
% 2.54/1.34  tff(f_107, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_orders_2)).
% 2.54/1.34  tff(f_90, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.54/1.34  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.54/1.34  tff(f_94, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 2.54/1.34  tff(f_48, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.54/1.34  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.54/1.34  tff(f_74, axiom, (![A]: (l1_orders_2(A) => (v3_orders_2(A) <=> r1_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_orders_2)).
% 2.54/1.34  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.54/1.34  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_relat_2(A, B) <=> (![C]: (r2_hidden(C, B) => r2_hidden(k4_tarski(C, C), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_2)).
% 2.54/1.34  tff(f_86, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_orders_2)).
% 2.54/1.34  tff(f_68, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.54/1.34  tff(c_38, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.54/1.34  tff(c_30, plain, (![A_46]: (l1_struct_0(A_46) | ~l1_orders_2(A_46))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.54/1.34  tff(c_42, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.54/1.34  tff(c_12, plain, (![A_25, B_26]: (v1_relat_1(k2_zfmisc_1(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.54/1.34  tff(c_32, plain, (![A_47]: (m1_subset_1(u1_orders_2(A_47), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_47), u1_struct_0(A_47)))) | ~l1_orders_2(A_47))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.54/1.34  tff(c_10, plain, (![A_7]: (r2_hidden('#skF_1'(A_7), A_7) | v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.54/1.34  tff(c_55, plain, (![C_61, A_62, B_63]: (r2_hidden(C_61, A_62) | ~r2_hidden(C_61, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.54/1.34  tff(c_61, plain, (![A_7, A_62]: (r2_hidden('#skF_1'(A_7), A_62) | ~m1_subset_1(A_7, k1_zfmisc_1(A_62)) | v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_10, c_55])).
% 2.54/1.34  tff(c_75, plain, (![A_72, B_73]: (k4_tarski('#skF_2'(A_72, B_73), '#skF_3'(A_72, B_73))=B_73 | ~r2_hidden(B_73, A_72) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.54/1.34  tff(c_8, plain, (![C_20, D_21, A_7]: (k4_tarski(C_20, D_21)!='#skF_1'(A_7) | v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.54/1.34  tff(c_79, plain, (![B_73, A_7, A_72]: (B_73!='#skF_1'(A_7) | v1_relat_1(A_7) | ~r2_hidden(B_73, A_72) | ~v1_relat_1(A_72))), inference(superposition, [status(thm), theory('equality')], [c_75, c_8])).
% 2.54/1.34  tff(c_103, plain, (![A_80, A_81]: (v1_relat_1(A_80) | ~r2_hidden('#skF_1'(A_80), A_81) | ~v1_relat_1(A_81))), inference(reflexivity, [status(thm), theory('equality')], [c_79])).
% 2.54/1.34  tff(c_117, plain, (![A_82, A_83]: (~v1_relat_1(A_82) | ~m1_subset_1(A_83, k1_zfmisc_1(A_82)) | v1_relat_1(A_83))), inference(resolution, [status(thm)], [c_61, c_103])).
% 2.54/1.34  tff(c_120, plain, (![A_47]: (~v1_relat_1(k2_zfmisc_1(u1_struct_0(A_47), u1_struct_0(A_47))) | v1_relat_1(u1_orders_2(A_47)) | ~l1_orders_2(A_47))), inference(resolution, [status(thm)], [c_32, c_117])).
% 2.54/1.34  tff(c_123, plain, (![A_47]: (v1_relat_1(u1_orders_2(A_47)) | ~l1_orders_2(A_47))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_120])).
% 2.54/1.34  tff(c_34, plain, (~r1_orders_2('#skF_5', '#skF_6', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.54/1.34  tff(c_40, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.54/1.34  tff(c_36, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.54/1.34  tff(c_24, plain, (![A_38]: (r1_relat_2(u1_orders_2(A_38), u1_struct_0(A_38)) | ~v3_orders_2(A_38) | ~l1_orders_2(A_38))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.54/1.34  tff(c_4, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.54/1.34  tff(c_85, plain, (![C_74, A_75, B_76]: (r2_hidden(k4_tarski(C_74, C_74), A_75) | ~r2_hidden(C_74, B_76) | ~r1_relat_2(A_75, B_76) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.54/1.34  tff(c_165, plain, (![A_100, A_101, B_102]: (r2_hidden(k4_tarski(A_100, A_100), A_101) | ~r1_relat_2(A_101, B_102) | ~v1_relat_1(A_101) | v1_xboole_0(B_102) | ~m1_subset_1(A_100, B_102))), inference(resolution, [status(thm)], [c_4, c_85])).
% 2.54/1.34  tff(c_252, plain, (![A_129, A_130]: (r2_hidden(k4_tarski(A_129, A_129), u1_orders_2(A_130)) | ~v1_relat_1(u1_orders_2(A_130)) | v1_xboole_0(u1_struct_0(A_130)) | ~m1_subset_1(A_129, u1_struct_0(A_130)) | ~v3_orders_2(A_130) | ~l1_orders_2(A_130))), inference(resolution, [status(thm)], [c_24, c_165])).
% 2.54/1.34  tff(c_26, plain, (![A_39, B_43, C_45]: (r1_orders_2(A_39, B_43, C_45) | ~r2_hidden(k4_tarski(B_43, C_45), u1_orders_2(A_39)) | ~m1_subset_1(C_45, u1_struct_0(A_39)) | ~m1_subset_1(B_43, u1_struct_0(A_39)) | ~l1_orders_2(A_39))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.54/1.34  tff(c_268, plain, (![A_131, A_132]: (r1_orders_2(A_131, A_132, A_132) | ~v1_relat_1(u1_orders_2(A_131)) | v1_xboole_0(u1_struct_0(A_131)) | ~m1_subset_1(A_132, u1_struct_0(A_131)) | ~v3_orders_2(A_131) | ~l1_orders_2(A_131))), inference(resolution, [status(thm)], [c_252, c_26])).
% 2.54/1.34  tff(c_270, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_6') | ~v1_relat_1(u1_orders_2('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~v3_orders_2('#skF_5') | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_36, c_268])).
% 2.54/1.34  tff(c_273, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_6') | ~v1_relat_1(u1_orders_2('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40, c_270])).
% 2.54/1.34  tff(c_274, plain, (~v1_relat_1(u1_orders_2('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_34, c_273])).
% 2.54/1.34  tff(c_275, plain, (~v1_relat_1(u1_orders_2('#skF_5'))), inference(splitLeft, [status(thm)], [c_274])).
% 2.54/1.34  tff(c_278, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_123, c_275])).
% 2.54/1.34  tff(c_282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_278])).
% 2.54/1.34  tff(c_283, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_274])).
% 2.54/1.34  tff(c_20, plain, (![A_37]: (~v1_xboole_0(u1_struct_0(A_37)) | ~l1_struct_0(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.54/1.34  tff(c_291, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_283, c_20])).
% 2.54/1.34  tff(c_294, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_291])).
% 2.54/1.34  tff(c_297, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_30, c_294])).
% 2.54/1.34  tff(c_301, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_297])).
% 2.54/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.34  
% 2.54/1.34  Inference rules
% 2.54/1.34  ----------------------
% 2.54/1.34  #Ref     : 1
% 2.54/1.34  #Sup     : 55
% 2.54/1.34  #Fact    : 0
% 2.54/1.34  #Define  : 0
% 2.54/1.34  #Split   : 1
% 2.54/1.34  #Chain   : 0
% 2.54/1.34  #Close   : 0
% 2.54/1.34  
% 2.54/1.34  Ordering : KBO
% 2.54/1.34  
% 2.54/1.34  Simplification rules
% 2.54/1.34  ----------------------
% 2.54/1.34  #Subsume      : 1
% 2.54/1.34  #Demod        : 8
% 2.54/1.34  #Tautology    : 6
% 2.54/1.34  #SimpNegUnit  : 2
% 2.54/1.34  #BackRed      : 0
% 2.54/1.34  
% 2.54/1.34  #Partial instantiations: 0
% 2.54/1.34  #Strategies tried      : 1
% 2.54/1.34  
% 2.54/1.34  Timing (in seconds)
% 2.54/1.34  ----------------------
% 2.54/1.35  Preprocessing        : 0.30
% 2.54/1.35  Parsing              : 0.17
% 2.54/1.35  CNF conversion       : 0.02
% 2.54/1.35  Main loop            : 0.29
% 2.54/1.35  Inferencing          : 0.12
% 2.54/1.35  Reduction            : 0.07
% 2.54/1.35  Demodulation         : 0.05
% 2.54/1.35  BG Simplification    : 0.02
% 2.54/1.35  Subsumption          : 0.06
% 2.54/1.35  Abstraction          : 0.01
% 2.54/1.35  MUC search           : 0.00
% 2.54/1.35  Cooper               : 0.00
% 2.54/1.35  Total                : 0.62
% 2.54/1.35  Index Insertion      : 0.00
% 2.54/1.35  Index Deletion       : 0.00
% 2.54/1.35  Index Matching       : 0.00
% 2.54/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
