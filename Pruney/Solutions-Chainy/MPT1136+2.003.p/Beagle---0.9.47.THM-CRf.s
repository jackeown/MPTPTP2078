%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:18 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 107 expanded)
%              Number of leaves         :   41 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  121 ( 237 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r2_hidden > r1_relat_2 > m1_subset_1 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_7 > #skF_1 > #skF_11 > #skF_4 > #skF_10 > #skF_2 > #skF_6 > #skF_8 > #skF_5 > #skF_3 > #skF_9 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_relat_2,type,(
    r1_relat_2: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v3_orders_2(A)
      <=> r1_relat_2(u1_orders_2(A),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_orders_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_relat_2(A,B)
        <=> ! [C] :
              ( r2_hidden(C,B)
             => r2_hidden(k4_tarski(C,C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
              <=> r2_hidden(k4_tarski(B,C),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_60,plain,(
    l1_orders_2('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_52,plain,(
    ! [A_77] :
      ( l1_struct_0(A_77)
      | ~ l1_orders_2(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_34,plain,(
    ! [A_40] :
      ( r2_hidden('#skF_7'(A_40),A_40)
      | v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_222,plain,(
    ! [A_148,B_149,D_150] :
      ( k4_tarski('#skF_5'(A_148,B_149,k2_zfmisc_1(A_148,B_149),D_150),'#skF_6'(A_148,B_149,k2_zfmisc_1(A_148,B_149),D_150)) = D_150
      | ~ r2_hidden(D_150,k2_zfmisc_1(A_148,B_149)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    ! [C_53,D_54,A_40] :
      ( k4_tarski(C_53,D_54) != '#skF_7'(A_40)
      | v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_235,plain,(
    ! [D_150,A_40,A_148,B_149] :
      ( D_150 != '#skF_7'(A_40)
      | v1_relat_1(A_40)
      | ~ r2_hidden(D_150,k2_zfmisc_1(A_148,B_149)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_32])).

tff(c_246,plain,(
    ! [A_155,A_156,B_157] :
      ( v1_relat_1(A_155)
      | ~ r2_hidden('#skF_7'(A_155),k2_zfmisc_1(A_156,B_157)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_235])).

tff(c_255,plain,(
    ! [A_156,B_157] : v1_relat_1(k2_zfmisc_1(A_156,B_157)) ),
    inference(resolution,[status(thm)],[c_34,c_246])).

tff(c_78,plain,(
    ! [A_94] :
      ( m1_subset_1(u1_orders_2(A_94),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_94),u1_struct_0(A_94))))
      | ~ l1_orders_2(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_28,plain,(
    ! [B_39,A_37] :
      ( v1_relat_1(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_37))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_82,plain,(
    ! [A_94] :
      ( v1_relat_1(u1_orders_2(A_94))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(A_94),u1_struct_0(A_94)))
      | ~ l1_orders_2(A_94) ) ),
    inference(resolution,[status(thm)],[c_78,c_28])).

tff(c_257,plain,(
    ! [A_94] :
      ( v1_relat_1(u1_orders_2(A_94))
      | ~ l1_orders_2(A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_82])).

tff(c_56,plain,(
    ~ r1_orders_2('#skF_11','#skF_12','#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_62,plain,(
    v3_orders_2('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_58,plain,(
    m1_subset_1('#skF_12',u1_struct_0('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_46,plain,(
    ! [A_69] :
      ( r1_relat_2(u1_orders_2(A_69),u1_struct_0(A_69))
      | ~ v3_orders_2(A_69)
      | ~ l1_orders_2(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_26,plain,(
    ! [A_35,B_36] :
      ( r2_hidden(A_35,B_36)
      | v1_xboole_0(B_36)
      | ~ m1_subset_1(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_85,plain,(
    ! [C_100,A_101,B_102] :
      ( r2_hidden(k4_tarski(C_100,C_100),A_101)
      | ~ r2_hidden(C_100,B_102)
      | ~ r1_relat_2(A_101,B_102)
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_156,plain,(
    ! [A_125,A_126,B_127] :
      ( r2_hidden(k4_tarski(A_125,A_125),A_126)
      | ~ r1_relat_2(A_126,B_127)
      | ~ v1_relat_1(A_126)
      | v1_xboole_0(B_127)
      | ~ m1_subset_1(A_125,B_127) ) ),
    inference(resolution,[status(thm)],[c_26,c_85])).

tff(c_271,plain,(
    ! [A_173,A_174] :
      ( r2_hidden(k4_tarski(A_173,A_173),u1_orders_2(A_174))
      | ~ v1_relat_1(u1_orders_2(A_174))
      | v1_xboole_0(u1_struct_0(A_174))
      | ~ m1_subset_1(A_173,u1_struct_0(A_174))
      | ~ v3_orders_2(A_174)
      | ~ l1_orders_2(A_174) ) ),
    inference(resolution,[status(thm)],[c_46,c_156])).

tff(c_48,plain,(
    ! [A_70,B_74,C_76] :
      ( r1_orders_2(A_70,B_74,C_76)
      | ~ r2_hidden(k4_tarski(B_74,C_76),u1_orders_2(A_70))
      | ~ m1_subset_1(C_76,u1_struct_0(A_70))
      | ~ m1_subset_1(B_74,u1_struct_0(A_70))
      | ~ l1_orders_2(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_284,plain,(
    ! [A_175,A_176] :
      ( r1_orders_2(A_175,A_176,A_176)
      | ~ v1_relat_1(u1_orders_2(A_175))
      | v1_xboole_0(u1_struct_0(A_175))
      | ~ m1_subset_1(A_176,u1_struct_0(A_175))
      | ~ v3_orders_2(A_175)
      | ~ l1_orders_2(A_175) ) ),
    inference(resolution,[status(thm)],[c_271,c_48])).

tff(c_286,plain,
    ( r1_orders_2('#skF_11','#skF_12','#skF_12')
    | ~ v1_relat_1(u1_orders_2('#skF_11'))
    | v1_xboole_0(u1_struct_0('#skF_11'))
    | ~ v3_orders_2('#skF_11')
    | ~ l1_orders_2('#skF_11') ),
    inference(resolution,[status(thm)],[c_58,c_284])).

tff(c_289,plain,
    ( r1_orders_2('#skF_11','#skF_12','#skF_12')
    | ~ v1_relat_1(u1_orders_2('#skF_11'))
    | v1_xboole_0(u1_struct_0('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_62,c_286])).

tff(c_290,plain,
    ( ~ v1_relat_1(u1_orders_2('#skF_11'))
    | v1_xboole_0(u1_struct_0('#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_289])).

tff(c_312,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_290])).

tff(c_315,plain,(
    ~ l1_orders_2('#skF_11') ),
    inference(resolution,[status(thm)],[c_257,c_312])).

tff(c_319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_315])).

tff(c_320,plain,(
    v1_xboole_0(u1_struct_0('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_42,plain,(
    ! [A_68] :
      ( ~ v1_xboole_0(u1_struct_0(A_68))
      | ~ l1_struct_0(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_324,plain,
    ( ~ l1_struct_0('#skF_11')
    | v2_struct_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_320,c_42])).

tff(c_327,plain,(
    ~ l1_struct_0('#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_324])).

tff(c_330,plain,(
    ~ l1_orders_2('#skF_11') ),
    inference(resolution,[status(thm)],[c_52,c_327])).

tff(c_334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_330])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:15:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.44  
% 2.78/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.44  %$ r1_orders_2 > r2_hidden > r1_relat_2 > m1_subset_1 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k4_tarski > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_7 > #skF_1 > #skF_11 > #skF_4 > #skF_10 > #skF_2 > #skF_6 > #skF_8 > #skF_5 > #skF_3 > #skF_9 > #skF_12
% 2.78/1.44  
% 2.78/1.44  %Foreground sorts:
% 2.78/1.44  
% 2.78/1.44  
% 2.78/1.44  %Background operators:
% 2.78/1.44  
% 2.78/1.44  
% 2.78/1.44  %Foreground operators:
% 2.78/1.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.78/1.44  tff('#skF_7', type, '#skF_7': $i > $i).
% 2.78/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.78/1.44  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.78/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.44  tff('#skF_11', type, '#skF_11': $i).
% 2.78/1.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.78/1.44  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.78/1.44  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.78/1.44  tff(r1_relat_2, type, r1_relat_2: ($i * $i) > $o).
% 2.78/1.44  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 2.78/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.78/1.44  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.78/1.44  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 2.78/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.78/1.44  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.78/1.44  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.78/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.44  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.78/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.78/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.78/1.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.78/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.44  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.78/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.78/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.78/1.44  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 2.78/1.44  tff('#skF_12', type, '#skF_12': $i).
% 2.78/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.44  
% 2.78/1.46  tff(f_117, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_orders_2)).
% 2.78/1.46  tff(f_100, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.78/1.46  tff(f_60, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.78/1.46  tff(f_37, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 2.78/1.46  tff(f_104, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 2.78/1.46  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.78/1.46  tff(f_84, axiom, (![A]: (l1_orders_2(A) => (v3_orders_2(A) <=> r1_relat_2(u1_orders_2(A), u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_orders_2)).
% 2.78/1.46  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.78/1.46  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_relat_2(A, B) <=> (![C]: (r2_hidden(C, B) => r2_hidden(k4_tarski(C, C), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_2)).
% 2.78/1.46  tff(f_96, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) <=> r2_hidden(k4_tarski(B, C), u1_orders_2(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_orders_2)).
% 2.78/1.46  tff(f_78, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.78/1.46  tff(c_60, plain, (l1_orders_2('#skF_11')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.78/1.46  tff(c_52, plain, (![A_77]: (l1_struct_0(A_77) | ~l1_orders_2(A_77))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.78/1.46  tff(c_64, plain, (~v2_struct_0('#skF_11')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.78/1.46  tff(c_34, plain, (![A_40]: (r2_hidden('#skF_7'(A_40), A_40) | v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.78/1.46  tff(c_222, plain, (![A_148, B_149, D_150]: (k4_tarski('#skF_5'(A_148, B_149, k2_zfmisc_1(A_148, B_149), D_150), '#skF_6'(A_148, B_149, k2_zfmisc_1(A_148, B_149), D_150))=D_150 | ~r2_hidden(D_150, k2_zfmisc_1(A_148, B_149)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.78/1.46  tff(c_32, plain, (![C_53, D_54, A_40]: (k4_tarski(C_53, D_54)!='#skF_7'(A_40) | v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.78/1.46  tff(c_235, plain, (![D_150, A_40, A_148, B_149]: (D_150!='#skF_7'(A_40) | v1_relat_1(A_40) | ~r2_hidden(D_150, k2_zfmisc_1(A_148, B_149)))), inference(superposition, [status(thm), theory('equality')], [c_222, c_32])).
% 2.78/1.46  tff(c_246, plain, (![A_155, A_156, B_157]: (v1_relat_1(A_155) | ~r2_hidden('#skF_7'(A_155), k2_zfmisc_1(A_156, B_157)))), inference(reflexivity, [status(thm), theory('equality')], [c_235])).
% 2.78/1.46  tff(c_255, plain, (![A_156, B_157]: (v1_relat_1(k2_zfmisc_1(A_156, B_157)))), inference(resolution, [status(thm)], [c_34, c_246])).
% 2.78/1.46  tff(c_78, plain, (![A_94]: (m1_subset_1(u1_orders_2(A_94), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_94), u1_struct_0(A_94)))) | ~l1_orders_2(A_94))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.78/1.46  tff(c_28, plain, (![B_39, A_37]: (v1_relat_1(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_37)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.78/1.46  tff(c_82, plain, (![A_94]: (v1_relat_1(u1_orders_2(A_94)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(A_94), u1_struct_0(A_94))) | ~l1_orders_2(A_94))), inference(resolution, [status(thm)], [c_78, c_28])).
% 2.78/1.46  tff(c_257, plain, (![A_94]: (v1_relat_1(u1_orders_2(A_94)) | ~l1_orders_2(A_94))), inference(demodulation, [status(thm), theory('equality')], [c_255, c_82])).
% 2.78/1.46  tff(c_56, plain, (~r1_orders_2('#skF_11', '#skF_12', '#skF_12')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.78/1.46  tff(c_62, plain, (v3_orders_2('#skF_11')), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.78/1.46  tff(c_58, plain, (m1_subset_1('#skF_12', u1_struct_0('#skF_11'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.78/1.46  tff(c_46, plain, (![A_69]: (r1_relat_2(u1_orders_2(A_69), u1_struct_0(A_69)) | ~v3_orders_2(A_69) | ~l1_orders_2(A_69))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.78/1.46  tff(c_26, plain, (![A_35, B_36]: (r2_hidden(A_35, B_36) | v1_xboole_0(B_36) | ~m1_subset_1(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.78/1.46  tff(c_85, plain, (![C_100, A_101, B_102]: (r2_hidden(k4_tarski(C_100, C_100), A_101) | ~r2_hidden(C_100, B_102) | ~r1_relat_2(A_101, B_102) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.78/1.46  tff(c_156, plain, (![A_125, A_126, B_127]: (r2_hidden(k4_tarski(A_125, A_125), A_126) | ~r1_relat_2(A_126, B_127) | ~v1_relat_1(A_126) | v1_xboole_0(B_127) | ~m1_subset_1(A_125, B_127))), inference(resolution, [status(thm)], [c_26, c_85])).
% 2.78/1.46  tff(c_271, plain, (![A_173, A_174]: (r2_hidden(k4_tarski(A_173, A_173), u1_orders_2(A_174)) | ~v1_relat_1(u1_orders_2(A_174)) | v1_xboole_0(u1_struct_0(A_174)) | ~m1_subset_1(A_173, u1_struct_0(A_174)) | ~v3_orders_2(A_174) | ~l1_orders_2(A_174))), inference(resolution, [status(thm)], [c_46, c_156])).
% 2.78/1.46  tff(c_48, plain, (![A_70, B_74, C_76]: (r1_orders_2(A_70, B_74, C_76) | ~r2_hidden(k4_tarski(B_74, C_76), u1_orders_2(A_70)) | ~m1_subset_1(C_76, u1_struct_0(A_70)) | ~m1_subset_1(B_74, u1_struct_0(A_70)) | ~l1_orders_2(A_70))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.78/1.46  tff(c_284, plain, (![A_175, A_176]: (r1_orders_2(A_175, A_176, A_176) | ~v1_relat_1(u1_orders_2(A_175)) | v1_xboole_0(u1_struct_0(A_175)) | ~m1_subset_1(A_176, u1_struct_0(A_175)) | ~v3_orders_2(A_175) | ~l1_orders_2(A_175))), inference(resolution, [status(thm)], [c_271, c_48])).
% 2.78/1.46  tff(c_286, plain, (r1_orders_2('#skF_11', '#skF_12', '#skF_12') | ~v1_relat_1(u1_orders_2('#skF_11')) | v1_xboole_0(u1_struct_0('#skF_11')) | ~v3_orders_2('#skF_11') | ~l1_orders_2('#skF_11')), inference(resolution, [status(thm)], [c_58, c_284])).
% 2.78/1.46  tff(c_289, plain, (r1_orders_2('#skF_11', '#skF_12', '#skF_12') | ~v1_relat_1(u1_orders_2('#skF_11')) | v1_xboole_0(u1_struct_0('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_62, c_286])).
% 2.78/1.46  tff(c_290, plain, (~v1_relat_1(u1_orders_2('#skF_11')) | v1_xboole_0(u1_struct_0('#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_56, c_289])).
% 2.78/1.46  tff(c_312, plain, (~v1_relat_1(u1_orders_2('#skF_11'))), inference(splitLeft, [status(thm)], [c_290])).
% 2.78/1.46  tff(c_315, plain, (~l1_orders_2('#skF_11')), inference(resolution, [status(thm)], [c_257, c_312])).
% 2.78/1.46  tff(c_319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_315])).
% 2.78/1.46  tff(c_320, plain, (v1_xboole_0(u1_struct_0('#skF_11'))), inference(splitRight, [status(thm)], [c_290])).
% 2.78/1.46  tff(c_42, plain, (![A_68]: (~v1_xboole_0(u1_struct_0(A_68)) | ~l1_struct_0(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.78/1.46  tff(c_324, plain, (~l1_struct_0('#skF_11') | v2_struct_0('#skF_11')), inference(resolution, [status(thm)], [c_320, c_42])).
% 2.78/1.46  tff(c_327, plain, (~l1_struct_0('#skF_11')), inference(negUnitSimplification, [status(thm)], [c_64, c_324])).
% 2.78/1.46  tff(c_330, plain, (~l1_orders_2('#skF_11')), inference(resolution, [status(thm)], [c_52, c_327])).
% 2.78/1.46  tff(c_334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_330])).
% 2.78/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.46  
% 2.78/1.46  Inference rules
% 2.78/1.46  ----------------------
% 2.78/1.46  #Ref     : 2
% 2.78/1.46  #Sup     : 59
% 2.78/1.46  #Fact    : 0
% 2.78/1.46  #Define  : 0
% 2.78/1.46  #Split   : 1
% 2.78/1.46  #Chain   : 0
% 2.78/1.46  #Close   : 0
% 2.78/1.46  
% 2.78/1.46  Ordering : KBO
% 2.78/1.46  
% 2.78/1.46  Simplification rules
% 2.78/1.46  ----------------------
% 2.78/1.46  #Subsume      : 0
% 2.78/1.46  #Demod        : 5
% 2.78/1.46  #Tautology    : 10
% 2.78/1.46  #SimpNegUnit  : 2
% 2.78/1.46  #BackRed      : 1
% 2.78/1.46  
% 2.78/1.46  #Partial instantiations: 0
% 2.78/1.46  #Strategies tried      : 1
% 2.78/1.46  
% 2.78/1.46  Timing (in seconds)
% 2.78/1.46  ----------------------
% 2.78/1.46  Preprocessing        : 0.36
% 2.78/1.46  Parsing              : 0.18
% 2.78/1.46  CNF conversion       : 0.03
% 2.78/1.46  Main loop            : 0.27
% 2.78/1.46  Inferencing          : 0.11
% 2.78/1.46  Reduction            : 0.07
% 2.78/1.46  Demodulation         : 0.04
% 2.78/1.46  BG Simplification    : 0.02
% 2.78/1.46  Subsumption          : 0.05
% 2.78/1.46  Abstraction          : 0.01
% 2.78/1.46  MUC search           : 0.00
% 2.78/1.46  Cooper               : 0.00
% 2.78/1.46  Total                : 0.66
% 2.78/1.46  Index Insertion      : 0.00
% 2.78/1.46  Index Deletion       : 0.00
% 2.78/1.46  Index Matching       : 0.00
% 2.78/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
