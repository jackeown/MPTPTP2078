%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:41 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 123 expanded)
%              Number of leaves         :   20 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  186 ( 461 expanded)
%              Number of equality atoms :   27 (  71 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_tsep_1 > k1_tsep_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_tsep_1,type,(
    k2_tsep_1: ( $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_144,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => k2_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tmap_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => k1_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( m1_pre_topc(B,C)
              <=> k1_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tsep_1)).

tff(f_128,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( ~ r1_tsep_1(B,C)
               => ( ( m1_pre_topc(B,C)
                   => k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) )
                  & ( k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                   => m1_pre_topc(B,C) )
                  & ( m1_pre_topc(C,B)
                   => k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) )
                  & ( k2_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
                   => m1_pre_topc(C,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tsep_1)).

tff(f_52,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( m1_pre_topc(B,C)
               => ( ~ r1_tsep_1(B,C)
                  & ~ r1_tsep_1(C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).

tff(c_24,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_22,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_28,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_31,plain,(
    ! [A_26,B_27] :
      ( k1_tsep_1(A_26,B_27,B_27) = g1_pre_topc(u1_struct_0(B_27),u1_pre_topc(B_27))
      | ~ m1_pre_topc(B_27,A_26)
      | v2_struct_0(B_27)
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_33,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k1_tsep_1('#skF_1','#skF_2','#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_31])).

tff(c_36,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k1_tsep_1('#skF_1','#skF_2','#skF_2')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_33])).

tff(c_37,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k1_tsep_1('#skF_1','#skF_2','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_24,c_36])).

tff(c_59,plain,(
    ! [B_38,C_39,A_40] :
      ( m1_pre_topc(B_38,C_39)
      | k1_tsep_1(A_40,B_38,C_39) != g1_pre_topc(u1_struct_0(C_39),u1_pre_topc(C_39))
      | ~ m1_pre_topc(C_39,A_40)
      | v2_struct_0(C_39)
      | ~ m1_pre_topc(B_38,A_40)
      | v2_struct_0(B_38)
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_61,plain,(
    ! [B_38,A_40] :
      ( m1_pre_topc(B_38,'#skF_2')
      | k1_tsep_1(A_40,B_38,'#skF_2') != k1_tsep_1('#skF_1','#skF_2','#skF_2')
      | ~ m1_pre_topc('#skF_2',A_40)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_38,A_40)
      | v2_struct_0(B_38)
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40)
      | v2_struct_0(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_59])).

tff(c_63,plain,(
    ! [B_41,A_42] :
      ( m1_pre_topc(B_41,'#skF_2')
      | k1_tsep_1(A_42,B_41,'#skF_2') != k1_tsep_1('#skF_1','#skF_2','#skF_2')
      | ~ m1_pre_topc('#skF_2',A_42)
      | ~ m1_pre_topc(B_41,A_42)
      | v2_struct_0(B_41)
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_61])).

tff(c_65,plain,(
    ! [B_41] :
      ( m1_pre_topc(B_41,'#skF_2')
      | k1_tsep_1('#skF_1',B_41,'#skF_2') != k1_tsep_1('#skF_1','#skF_2','#skF_2')
      | ~ m1_pre_topc(B_41,'#skF_1')
      | v2_struct_0(B_41)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_63])).

tff(c_68,plain,(
    ! [B_41] :
      ( m1_pre_topc(B_41,'#skF_2')
      | k1_tsep_1('#skF_1',B_41,'#skF_2') != k1_tsep_1('#skF_1','#skF_2','#skF_2')
      | ~ m1_pre_topc(B_41,'#skF_1')
      | v2_struct_0(B_41)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_65])).

tff(c_69,plain,(
    ! [B_41] :
      ( m1_pre_topc(B_41,'#skF_2')
      | k1_tsep_1('#skF_1',B_41,'#skF_2') != k1_tsep_1('#skF_1','#skF_2','#skF_2')
      | ~ m1_pre_topc(B_41,'#skF_1')
      | v2_struct_0(B_41) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_68])).

tff(c_20,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k2_tsep_1('#skF_1','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_38,plain,(
    k2_tsep_1('#skF_1','#skF_2','#skF_2') != k1_tsep_1('#skF_1','#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_20])).

tff(c_126,plain,(
    ! [A_50,B_51,C_52] :
      ( k2_tsep_1(A_50,B_51,C_52) = g1_pre_topc(u1_struct_0(C_52),u1_pre_topc(C_52))
      | ~ m1_pre_topc(C_52,B_51)
      | r1_tsep_1(B_51,C_52)
      | ~ m1_pre_topc(C_52,A_50)
      | v2_struct_0(C_52)
      | ~ m1_pre_topc(B_51,A_50)
      | v2_struct_0(B_51)
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_130,plain,(
    ! [B_51] :
      ( k2_tsep_1('#skF_1',B_51,'#skF_2') = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ m1_pre_topc('#skF_2',B_51)
      | r1_tsep_1(B_51,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_51,'#skF_1')
      | v2_struct_0(B_51)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_126])).

tff(c_135,plain,(
    ! [B_51] :
      ( k2_tsep_1('#skF_1',B_51,'#skF_2') = k1_tsep_1('#skF_1','#skF_2','#skF_2')
      | ~ m1_pre_topc('#skF_2',B_51)
      | r1_tsep_1(B_51,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_51,'#skF_1')
      | v2_struct_0(B_51)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_37,c_130])).

tff(c_137,plain,(
    ! [B_53] :
      ( k2_tsep_1('#skF_1',B_53,'#skF_2') = k1_tsep_1('#skF_1','#skF_2','#skF_2')
      | ~ m1_pre_topc('#skF_2',B_53)
      | r1_tsep_1(B_53,'#skF_2')
      | ~ m1_pre_topc(B_53,'#skF_1')
      | v2_struct_0(B_53) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_24,c_135])).

tff(c_2,plain,(
    ! [C_7,B_5,A_1] :
      ( ~ r1_tsep_1(C_7,B_5)
      | ~ m1_pre_topc(B_5,C_7)
      | ~ m1_pre_topc(C_7,A_1)
      | v2_struct_0(C_7)
      | ~ m1_pre_topc(B_5,A_1)
      | v2_struct_0(B_5)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_139,plain,(
    ! [B_53,A_1] :
      ( ~ m1_pre_topc(B_53,A_1)
      | ~ m1_pre_topc('#skF_2',A_1)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1)
      | k2_tsep_1('#skF_1',B_53,'#skF_2') = k1_tsep_1('#skF_1','#skF_2','#skF_2')
      | ~ m1_pre_topc('#skF_2',B_53)
      | ~ m1_pre_topc(B_53,'#skF_1')
      | v2_struct_0(B_53) ) ),
    inference(resolution,[status(thm)],[c_137,c_2])).

tff(c_148,plain,(
    ! [B_54,A_55] :
      ( ~ m1_pre_topc(B_54,A_55)
      | ~ m1_pre_topc('#skF_2',A_55)
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55)
      | v2_struct_0(A_55)
      | k2_tsep_1('#skF_1',B_54,'#skF_2') = k1_tsep_1('#skF_1','#skF_2','#skF_2')
      | ~ m1_pre_topc('#skF_2',B_54)
      | ~ m1_pre_topc(B_54,'#skF_1')
      | v2_struct_0(B_54) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_139])).

tff(c_152,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | k2_tsep_1('#skF_1','#skF_2','#skF_2') = k1_tsep_1('#skF_1','#skF_2','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_148])).

tff(c_157,plain,
    ( v2_struct_0('#skF_1')
    | k2_tsep_1('#skF_1','#skF_2','#skF_2') = k1_tsep_1('#skF_1','#skF_2','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_28,c_26,c_152])).

tff(c_158,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_38,c_30,c_157])).

tff(c_161,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_69,c_158])).

tff(c_164,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_161])).

tff(c_166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:36:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.25  
% 2.33/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.26  %$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_tsep_1 > k1_tsep_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_1
% 2.33/1.26  
% 2.33/1.26  %Foreground sorts:
% 2.33/1.26  
% 2.33/1.26  
% 2.33/1.26  %Background operators:
% 2.33/1.26  
% 2.33/1.26  
% 2.33/1.26  %Foreground operators:
% 2.33/1.26  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.33/1.26  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 2.33/1.26  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.33/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.26  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.33/1.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.33/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.33/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.33/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.26  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.33/1.26  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 2.33/1.26  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.33/1.26  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.33/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.33/1.26  
% 2.33/1.27  tff(f_144, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k2_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tmap_1)).
% 2.33/1.27  tff(f_90, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k1_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tmap_1)).
% 2.33/1.27  tff(f_75, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) <=> (k1_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tsep_1)).
% 2.33/1.27  tff(f_128, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => ((((m1_pre_topc(B, C) => (k2_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))) & ((k2_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => m1_pre_topc(B, C))) & (m1_pre_topc(C, B) => (k2_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))))) & ((k2_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => m1_pre_topc(C, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tsep_1)).
% 2.33/1.27  tff(f_52, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tmap_1)).
% 2.33/1.27  tff(c_24, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.33/1.27  tff(c_22, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.33/1.27  tff(c_30, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.33/1.27  tff(c_28, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.33/1.27  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.33/1.27  tff(c_31, plain, (![A_26, B_27]: (k1_tsep_1(A_26, B_27, B_27)=g1_pre_topc(u1_struct_0(B_27), u1_pre_topc(B_27)) | ~m1_pre_topc(B_27, A_26) | v2_struct_0(B_27) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.33/1.27  tff(c_33, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_31])).
% 2.33/1.27  tff(c_36, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_33])).
% 2.33/1.27  tff(c_37, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k1_tsep_1('#skF_1', '#skF_2', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_30, c_24, c_36])).
% 2.33/1.27  tff(c_59, plain, (![B_38, C_39, A_40]: (m1_pre_topc(B_38, C_39) | k1_tsep_1(A_40, B_38, C_39)!=g1_pre_topc(u1_struct_0(C_39), u1_pre_topc(C_39)) | ~m1_pre_topc(C_39, A_40) | v2_struct_0(C_39) | ~m1_pre_topc(B_38, A_40) | v2_struct_0(B_38) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.33/1.27  tff(c_61, plain, (![B_38, A_40]: (m1_pre_topc(B_38, '#skF_2') | k1_tsep_1(A_40, B_38, '#skF_2')!=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | ~m1_pre_topc('#skF_2', A_40) | v2_struct_0('#skF_2') | ~m1_pre_topc(B_38, A_40) | v2_struct_0(B_38) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40) | v2_struct_0(A_40))), inference(superposition, [status(thm), theory('equality')], [c_37, c_59])).
% 2.33/1.27  tff(c_63, plain, (![B_41, A_42]: (m1_pre_topc(B_41, '#skF_2') | k1_tsep_1(A_42, B_41, '#skF_2')!=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | ~m1_pre_topc('#skF_2', A_42) | ~m1_pre_topc(B_41, A_42) | v2_struct_0(B_41) | ~l1_pre_topc(A_42) | ~v2_pre_topc(A_42) | v2_struct_0(A_42))), inference(negUnitSimplification, [status(thm)], [c_24, c_61])).
% 2.33/1.27  tff(c_65, plain, (![B_41]: (m1_pre_topc(B_41, '#skF_2') | k1_tsep_1('#skF_1', B_41, '#skF_2')!=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | ~m1_pre_topc(B_41, '#skF_1') | v2_struct_0(B_41) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_63])).
% 2.33/1.27  tff(c_68, plain, (![B_41]: (m1_pre_topc(B_41, '#skF_2') | k1_tsep_1('#skF_1', B_41, '#skF_2')!=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | ~m1_pre_topc(B_41, '#skF_1') | v2_struct_0(B_41) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_65])).
% 2.33/1.27  tff(c_69, plain, (![B_41]: (m1_pre_topc(B_41, '#skF_2') | k1_tsep_1('#skF_1', B_41, '#skF_2')!=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | ~m1_pre_topc(B_41, '#skF_1') | v2_struct_0(B_41))), inference(negUnitSimplification, [status(thm)], [c_30, c_68])).
% 2.33/1.27  tff(c_20, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k2_tsep_1('#skF_1', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.33/1.27  tff(c_38, plain, (k2_tsep_1('#skF_1', '#skF_2', '#skF_2')!=k1_tsep_1('#skF_1', '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_37, c_20])).
% 2.33/1.27  tff(c_126, plain, (![A_50, B_51, C_52]: (k2_tsep_1(A_50, B_51, C_52)=g1_pre_topc(u1_struct_0(C_52), u1_pre_topc(C_52)) | ~m1_pre_topc(C_52, B_51) | r1_tsep_1(B_51, C_52) | ~m1_pre_topc(C_52, A_50) | v2_struct_0(C_52) | ~m1_pre_topc(B_51, A_50) | v2_struct_0(B_51) | ~l1_pre_topc(A_50) | ~v2_pre_topc(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.33/1.27  tff(c_130, plain, (![B_51]: (k2_tsep_1('#skF_1', B_51, '#skF_2')=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~m1_pre_topc('#skF_2', B_51) | r1_tsep_1(B_51, '#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_51, '#skF_1') | v2_struct_0(B_51) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_126])).
% 2.33/1.27  tff(c_135, plain, (![B_51]: (k2_tsep_1('#skF_1', B_51, '#skF_2')=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | ~m1_pre_topc('#skF_2', B_51) | r1_tsep_1(B_51, '#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_51, '#skF_1') | v2_struct_0(B_51) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_37, c_130])).
% 2.33/1.27  tff(c_137, plain, (![B_53]: (k2_tsep_1('#skF_1', B_53, '#skF_2')=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | ~m1_pre_topc('#skF_2', B_53) | r1_tsep_1(B_53, '#skF_2') | ~m1_pre_topc(B_53, '#skF_1') | v2_struct_0(B_53))), inference(negUnitSimplification, [status(thm)], [c_30, c_24, c_135])).
% 2.33/1.27  tff(c_2, plain, (![C_7, B_5, A_1]: (~r1_tsep_1(C_7, B_5) | ~m1_pre_topc(B_5, C_7) | ~m1_pre_topc(C_7, A_1) | v2_struct_0(C_7) | ~m1_pre_topc(B_5, A_1) | v2_struct_0(B_5) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.33/1.27  tff(c_139, plain, (![B_53, A_1]: (~m1_pre_topc(B_53, A_1) | ~m1_pre_topc('#skF_2', A_1) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1) | k2_tsep_1('#skF_1', B_53, '#skF_2')=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | ~m1_pre_topc('#skF_2', B_53) | ~m1_pre_topc(B_53, '#skF_1') | v2_struct_0(B_53))), inference(resolution, [status(thm)], [c_137, c_2])).
% 2.33/1.27  tff(c_148, plain, (![B_54, A_55]: (~m1_pre_topc(B_54, A_55) | ~m1_pre_topc('#skF_2', A_55) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55) | v2_struct_0(A_55) | k2_tsep_1('#skF_1', B_54, '#skF_2')=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | ~m1_pre_topc('#skF_2', B_54) | ~m1_pre_topc(B_54, '#skF_1') | v2_struct_0(B_54))), inference(negUnitSimplification, [status(thm)], [c_24, c_139])).
% 2.33/1.27  tff(c_152, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | k2_tsep_1('#skF_1', '#skF_2', '#skF_2')=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_22, c_148])).
% 2.33/1.27  tff(c_157, plain, (v2_struct_0('#skF_1') | k2_tsep_1('#skF_1', '#skF_2', '#skF_2')=k1_tsep_1('#skF_1', '#skF_2', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_28, c_26, c_152])).
% 2.33/1.27  tff(c_158, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_24, c_38, c_30, c_157])).
% 2.33/1.27  tff(c_161, plain, (~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_69, c_158])).
% 2.33/1.27  tff(c_164, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_161])).
% 2.33/1.27  tff(c_166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_164])).
% 2.33/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.27  
% 2.33/1.27  Inference rules
% 2.33/1.27  ----------------------
% 2.33/1.27  #Ref     : 0
% 2.33/1.27  #Sup     : 23
% 2.33/1.27  #Fact    : 0
% 2.33/1.27  #Define  : 0
% 2.33/1.27  #Split   : 3
% 2.33/1.27  #Chain   : 0
% 2.33/1.27  #Close   : 0
% 2.33/1.27  
% 2.33/1.27  Ordering : KBO
% 2.33/1.27  
% 2.33/1.27  Simplification rules
% 2.33/1.27  ----------------------
% 2.33/1.27  #Subsume      : 4
% 2.33/1.27  #Demod        : 20
% 2.33/1.27  #Tautology    : 4
% 2.33/1.27  #SimpNegUnit  : 21
% 2.33/1.27  #BackRed      : 1
% 2.33/1.27  
% 2.33/1.27  #Partial instantiations: 0
% 2.33/1.27  #Strategies tried      : 1
% 2.33/1.27  
% 2.33/1.27  Timing (in seconds)
% 2.33/1.27  ----------------------
% 2.33/1.27  Preprocessing        : 0.31
% 2.33/1.27  Parsing              : 0.17
% 2.33/1.27  CNF conversion       : 0.02
% 2.33/1.27  Main loop            : 0.20
% 2.33/1.27  Inferencing          : 0.08
% 2.33/1.27  Reduction            : 0.05
% 2.33/1.27  Demodulation         : 0.04
% 2.33/1.28  BG Simplification    : 0.02
% 2.33/1.28  Subsumption          : 0.05
% 2.33/1.28  Abstraction          : 0.01
% 2.33/1.28  MUC search           : 0.00
% 2.33/1.28  Cooper               : 0.00
% 2.33/1.28  Total                : 0.54
% 2.33/1.28  Index Insertion      : 0.00
% 2.33/1.28  Index Deletion       : 0.00
% 2.33/1.28  Index Matching       : 0.00
% 2.33/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
