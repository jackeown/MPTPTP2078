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
% DateTime   : Thu Dec  3 10:30:47 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 189 expanded)
%              Number of leaves         :   33 (  80 expanded)
%              Depth                    :   13
%              Number of atoms          :  162 ( 728 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_waybel_0 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_waybel_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k2_waybel_0,type,(
    k2_waybel_0: ( $i * $i * $i ) > $i )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_129,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_orders_2(B)
              & v7_waybel_0(B)
              & l1_waybel_0(B,A) )
           => r1_waybel_0(A,B,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc4_struct_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r1_waybel_0(A,B,C)
            <=> ? [D] :
                  ( m1_subset_1(D,u1_struct_0(B))
                  & ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ( r1_orders_2(B,D,E)
                       => r2_hidden(k2_waybel_0(A,B,E),C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_waybel_0)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A)
        & m1_subset_1(C,u1_struct_0(B)) )
     => m1_subset_1(k2_waybel_0(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_waybel_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_51,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_42,plain,(
    l1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_34,plain,(
    l1_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_53,plain,(
    ! [B_79,A_80] :
      ( l1_orders_2(B_79)
      | ~ l1_waybel_0(B_79,A_80)
      | ~ l1_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_56,plain,
    ( l1_orders_2('#skF_6')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_53])).

tff(c_59,plain,(
    l1_orders_2('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_56])).

tff(c_16,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_11] :
      ( m1_subset_1('#skF_2'(A_11),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_struct_0(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_67,plain,(
    ! [A_85,C_86,B_87] :
      ( m1_subset_1(A_85,C_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(C_86))
      | ~ r2_hidden(A_85,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_71,plain,(
    ! [A_88,A_89] :
      ( m1_subset_1(A_88,u1_struct_0(A_89))
      | ~ r2_hidden(A_88,'#skF_2'(A_89))
      | ~ l1_struct_0(A_89)
      | v2_struct_0(A_89) ) ),
    inference(resolution,[status(thm)],[c_14,c_67])).

tff(c_81,plain,(
    ! [A_89] :
      ( m1_subset_1('#skF_1'('#skF_2'(A_89)),u1_struct_0(A_89))
      | ~ l1_struct_0(A_89)
      | v2_struct_0(A_89)
      | v1_xboole_0('#skF_2'(A_89)) ) ),
    inference(resolution,[status(thm)],[c_4,c_71])).

tff(c_26,plain,(
    ! [A_14,B_42,C_56,D_63] :
      ( m1_subset_1('#skF_3'(A_14,B_42,C_56,D_63),u1_struct_0(B_42))
      | r1_waybel_0(A_14,B_42,C_56)
      | ~ m1_subset_1(D_63,u1_struct_0(B_42))
      | ~ l1_waybel_0(B_42,A_14)
      | v2_struct_0(B_42)
      | ~ l1_struct_0(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_28,plain,(
    ! [A_67,B_68,C_69] :
      ( m1_subset_1(k2_waybel_0(A_67,B_68,C_69),u1_struct_0(A_67))
      | ~ m1_subset_1(C_69,u1_struct_0(B_68))
      | ~ l1_waybel_0(B_68,A_67)
      | v2_struct_0(B_68)
      | ~ l1_struct_0(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_88,plain,(
    ! [A_107,B_108,C_109,D_110] :
      ( ~ r2_hidden(k2_waybel_0(A_107,B_108,'#skF_3'(A_107,B_108,C_109,D_110)),C_109)
      | r1_waybel_0(A_107,B_108,C_109)
      | ~ m1_subset_1(D_110,u1_struct_0(B_108))
      | ~ l1_waybel_0(B_108,A_107)
      | v2_struct_0(B_108)
      | ~ l1_struct_0(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_100,plain,(
    ! [A_115,B_116,B_117,D_118] :
      ( r1_waybel_0(A_115,B_116,B_117)
      | ~ m1_subset_1(D_118,u1_struct_0(B_116))
      | ~ l1_waybel_0(B_116,A_115)
      | v2_struct_0(B_116)
      | ~ l1_struct_0(A_115)
      | v2_struct_0(A_115)
      | v1_xboole_0(B_117)
      | ~ m1_subset_1(k2_waybel_0(A_115,B_116,'#skF_3'(A_115,B_116,B_117,D_118)),B_117) ) ),
    inference(resolution,[status(thm)],[c_6,c_88])).

tff(c_111,plain,(
    ! [A_119,B_120,D_121] :
      ( r1_waybel_0(A_119,B_120,u1_struct_0(A_119))
      | ~ m1_subset_1(D_121,u1_struct_0(B_120))
      | v1_xboole_0(u1_struct_0(A_119))
      | ~ m1_subset_1('#skF_3'(A_119,B_120,u1_struct_0(A_119),D_121),u1_struct_0(B_120))
      | ~ l1_waybel_0(B_120,A_119)
      | v2_struct_0(B_120)
      | ~ l1_struct_0(A_119)
      | v2_struct_0(A_119) ) ),
    inference(resolution,[status(thm)],[c_28,c_100])).

tff(c_122,plain,(
    ! [A_122,B_123,D_124] :
      ( v1_xboole_0(u1_struct_0(A_122))
      | r1_waybel_0(A_122,B_123,u1_struct_0(A_122))
      | ~ m1_subset_1(D_124,u1_struct_0(B_123))
      | ~ l1_waybel_0(B_123,A_122)
      | v2_struct_0(B_123)
      | ~ l1_struct_0(A_122)
      | v2_struct_0(A_122) ) ),
    inference(resolution,[status(thm)],[c_26,c_111])).

tff(c_154,plain,(
    ! [A_129,A_130] :
      ( v1_xboole_0(u1_struct_0(A_129))
      | r1_waybel_0(A_129,A_130,u1_struct_0(A_129))
      | ~ l1_waybel_0(A_130,A_129)
      | ~ l1_struct_0(A_129)
      | v2_struct_0(A_129)
      | ~ l1_struct_0(A_130)
      | v2_struct_0(A_130)
      | v1_xboole_0('#skF_2'(A_130)) ) ),
    inference(resolution,[status(thm)],[c_81,c_122])).

tff(c_32,plain,(
    ~ r1_waybel_0('#skF_5','#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_157,plain,
    ( v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6')
    | v1_xboole_0('#skF_2'('#skF_6')) ),
    inference(resolution,[status(thm)],[c_154,c_32])).

tff(c_160,plain,
    ( v1_xboole_0(u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6')
    | v1_xboole_0('#skF_2'('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_34,c_157])).

tff(c_161,plain,
    ( v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_6')
    | v1_xboole_0('#skF_2'('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_44,c_160])).

tff(c_162,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_165,plain,(
    ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_16,c_162])).

tff(c_169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_165])).

tff(c_171,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_170,plain,
    ( v1_xboole_0('#skF_2'('#skF_6'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_172,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_10,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_190,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_172,c_10])).

tff(c_193,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_190])).

tff(c_195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_193])).

tff(c_196,plain,(
    v1_xboole_0('#skF_2'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_12,plain,(
    ! [A_11] :
      ( ~ v1_xboole_0('#skF_2'(A_11))
      | ~ l1_struct_0(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_200,plain,
    ( ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_196,c_12])).

tff(c_203,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_200])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_203])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:21:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.29  
% 2.46/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.29  %$ r1_waybel_0 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_waybel_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_3
% 2.46/1.29  
% 2.46/1.29  %Foreground sorts:
% 2.46/1.29  
% 2.46/1.29  
% 2.46/1.29  %Background operators:
% 2.46/1.29  
% 2.46/1.29  
% 2.46/1.29  %Foreground operators:
% 2.46/1.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.46/1.29  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.46/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.46/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.46/1.29  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.46/1.29  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.46/1.29  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.46/1.29  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.46/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.46/1.29  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.46/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.46/1.29  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.46/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.46/1.29  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.46/1.29  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.46/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.29  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.46/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.46/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.46/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.46/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.46/1.29  
% 2.46/1.31  tff(f_129, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.46/1.31  tff(f_111, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 2.46/1.31  tff(f_66, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.46/1.31  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.46/1.31  tff(f_62, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc4_struct_0)).
% 2.46/1.31  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.46/1.31  tff(f_90, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) <=> (?[D]: (m1_subset_1(D, u1_struct_0(B)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r1_orders_2(B, D, E) => r2_hidden(k2_waybel_0(A, B, E), C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_waybel_0)).
% 2.46/1.31  tff(f_104, axiom, (![A, B, C]: (((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & l1_waybel_0(B, A)) & m1_subset_1(C, u1_struct_0(B))) => m1_subset_1(k2_waybel_0(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_waybel_0)).
% 2.46/1.31  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.46/1.31  tff(f_51, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.46/1.31  tff(c_40, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.46/1.31  tff(c_42, plain, (l1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.46/1.31  tff(c_34, plain, (l1_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.46/1.31  tff(c_53, plain, (![B_79, A_80]: (l1_orders_2(B_79) | ~l1_waybel_0(B_79, A_80) | ~l1_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.46/1.31  tff(c_56, plain, (l1_orders_2('#skF_6') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_34, c_53])).
% 2.46/1.31  tff(c_59, plain, (l1_orders_2('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_56])).
% 2.46/1.31  tff(c_16, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_orders_2(A_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.46/1.31  tff(c_44, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.46/1.31  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.46/1.31  tff(c_14, plain, (![A_11]: (m1_subset_1('#skF_2'(A_11), k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_struct_0(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.46/1.31  tff(c_67, plain, (![A_85, C_86, B_87]: (m1_subset_1(A_85, C_86) | ~m1_subset_1(B_87, k1_zfmisc_1(C_86)) | ~r2_hidden(A_85, B_87))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.46/1.31  tff(c_71, plain, (![A_88, A_89]: (m1_subset_1(A_88, u1_struct_0(A_89)) | ~r2_hidden(A_88, '#skF_2'(A_89)) | ~l1_struct_0(A_89) | v2_struct_0(A_89))), inference(resolution, [status(thm)], [c_14, c_67])).
% 2.46/1.31  tff(c_81, plain, (![A_89]: (m1_subset_1('#skF_1'('#skF_2'(A_89)), u1_struct_0(A_89)) | ~l1_struct_0(A_89) | v2_struct_0(A_89) | v1_xboole_0('#skF_2'(A_89)))), inference(resolution, [status(thm)], [c_4, c_71])).
% 2.46/1.31  tff(c_26, plain, (![A_14, B_42, C_56, D_63]: (m1_subset_1('#skF_3'(A_14, B_42, C_56, D_63), u1_struct_0(B_42)) | r1_waybel_0(A_14, B_42, C_56) | ~m1_subset_1(D_63, u1_struct_0(B_42)) | ~l1_waybel_0(B_42, A_14) | v2_struct_0(B_42) | ~l1_struct_0(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.46/1.31  tff(c_28, plain, (![A_67, B_68, C_69]: (m1_subset_1(k2_waybel_0(A_67, B_68, C_69), u1_struct_0(A_67)) | ~m1_subset_1(C_69, u1_struct_0(B_68)) | ~l1_waybel_0(B_68, A_67) | v2_struct_0(B_68) | ~l1_struct_0(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.46/1.31  tff(c_6, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.46/1.31  tff(c_88, plain, (![A_107, B_108, C_109, D_110]: (~r2_hidden(k2_waybel_0(A_107, B_108, '#skF_3'(A_107, B_108, C_109, D_110)), C_109) | r1_waybel_0(A_107, B_108, C_109) | ~m1_subset_1(D_110, u1_struct_0(B_108)) | ~l1_waybel_0(B_108, A_107) | v2_struct_0(B_108) | ~l1_struct_0(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.46/1.31  tff(c_100, plain, (![A_115, B_116, B_117, D_118]: (r1_waybel_0(A_115, B_116, B_117) | ~m1_subset_1(D_118, u1_struct_0(B_116)) | ~l1_waybel_0(B_116, A_115) | v2_struct_0(B_116) | ~l1_struct_0(A_115) | v2_struct_0(A_115) | v1_xboole_0(B_117) | ~m1_subset_1(k2_waybel_0(A_115, B_116, '#skF_3'(A_115, B_116, B_117, D_118)), B_117))), inference(resolution, [status(thm)], [c_6, c_88])).
% 2.46/1.31  tff(c_111, plain, (![A_119, B_120, D_121]: (r1_waybel_0(A_119, B_120, u1_struct_0(A_119)) | ~m1_subset_1(D_121, u1_struct_0(B_120)) | v1_xboole_0(u1_struct_0(A_119)) | ~m1_subset_1('#skF_3'(A_119, B_120, u1_struct_0(A_119), D_121), u1_struct_0(B_120)) | ~l1_waybel_0(B_120, A_119) | v2_struct_0(B_120) | ~l1_struct_0(A_119) | v2_struct_0(A_119))), inference(resolution, [status(thm)], [c_28, c_100])).
% 2.46/1.31  tff(c_122, plain, (![A_122, B_123, D_124]: (v1_xboole_0(u1_struct_0(A_122)) | r1_waybel_0(A_122, B_123, u1_struct_0(A_122)) | ~m1_subset_1(D_124, u1_struct_0(B_123)) | ~l1_waybel_0(B_123, A_122) | v2_struct_0(B_123) | ~l1_struct_0(A_122) | v2_struct_0(A_122))), inference(resolution, [status(thm)], [c_26, c_111])).
% 2.46/1.31  tff(c_154, plain, (![A_129, A_130]: (v1_xboole_0(u1_struct_0(A_129)) | r1_waybel_0(A_129, A_130, u1_struct_0(A_129)) | ~l1_waybel_0(A_130, A_129) | ~l1_struct_0(A_129) | v2_struct_0(A_129) | ~l1_struct_0(A_130) | v2_struct_0(A_130) | v1_xboole_0('#skF_2'(A_130)))), inference(resolution, [status(thm)], [c_81, c_122])).
% 2.46/1.31  tff(c_32, plain, (~r1_waybel_0('#skF_5', '#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.46/1.31  tff(c_157, plain, (v1_xboole_0(u1_struct_0('#skF_5')) | ~l1_waybel_0('#skF_6', '#skF_5') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6') | v1_xboole_0('#skF_2'('#skF_6'))), inference(resolution, [status(thm)], [c_154, c_32])).
% 2.46/1.31  tff(c_160, plain, (v1_xboole_0(u1_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6') | v1_xboole_0('#skF_2'('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_34, c_157])).
% 2.46/1.31  tff(c_161, plain, (v1_xboole_0(u1_struct_0('#skF_5')) | ~l1_struct_0('#skF_6') | v1_xboole_0('#skF_2'('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_40, c_44, c_160])).
% 2.46/1.31  tff(c_162, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_161])).
% 2.46/1.31  tff(c_165, plain, (~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_16, c_162])).
% 2.46/1.31  tff(c_169, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_165])).
% 2.46/1.31  tff(c_171, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_161])).
% 2.46/1.31  tff(c_170, plain, (v1_xboole_0('#skF_2'('#skF_6')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_161])).
% 2.46/1.31  tff(c_172, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_170])).
% 2.46/1.31  tff(c_10, plain, (![A_10]: (~v1_xboole_0(u1_struct_0(A_10)) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.46/1.31  tff(c_190, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_172, c_10])).
% 2.46/1.31  tff(c_193, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_190])).
% 2.46/1.31  tff(c_195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_193])).
% 2.46/1.31  tff(c_196, plain, (v1_xboole_0('#skF_2'('#skF_6'))), inference(splitRight, [status(thm)], [c_170])).
% 2.46/1.31  tff(c_12, plain, (![A_11]: (~v1_xboole_0('#skF_2'(A_11)) | ~l1_struct_0(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.46/1.31  tff(c_200, plain, (~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_196, c_12])).
% 2.46/1.31  tff(c_203, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_200])).
% 2.46/1.31  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_203])).
% 2.46/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.31  
% 2.46/1.31  Inference rules
% 2.46/1.31  ----------------------
% 2.46/1.31  #Ref     : 0
% 2.46/1.31  #Sup     : 29
% 2.46/1.31  #Fact    : 0
% 2.46/1.31  #Define  : 0
% 2.46/1.31  #Split   : 2
% 2.46/1.31  #Chain   : 0
% 2.46/1.31  #Close   : 0
% 2.46/1.31  
% 2.46/1.31  Ordering : KBO
% 2.46/1.31  
% 2.46/1.31  Simplification rules
% 2.46/1.31  ----------------------
% 2.46/1.31  #Subsume      : 3
% 2.46/1.31  #Demod        : 6
% 2.46/1.31  #Tautology    : 3
% 2.46/1.31  #SimpNegUnit  : 3
% 2.46/1.31  #BackRed      : 0
% 2.46/1.31  
% 2.46/1.31  #Partial instantiations: 0
% 2.46/1.31  #Strategies tried      : 1
% 2.46/1.31  
% 2.46/1.31  Timing (in seconds)
% 2.46/1.31  ----------------------
% 2.46/1.31  Preprocessing        : 0.30
% 2.46/1.31  Parsing              : 0.17
% 2.46/1.31  CNF conversion       : 0.03
% 2.46/1.31  Main loop            : 0.23
% 2.46/1.31  Inferencing          : 0.10
% 2.46/1.31  Reduction            : 0.05
% 2.46/1.31  Demodulation         : 0.04
% 2.46/1.31  BG Simplification    : 0.01
% 2.46/1.31  Subsumption          : 0.05
% 2.46/1.31  Abstraction          : 0.01
% 2.46/1.31  MUC search           : 0.00
% 2.46/1.31  Cooper               : 0.00
% 2.46/1.31  Total                : 0.57
% 2.46/1.31  Index Insertion      : 0.00
% 2.46/1.31  Index Deletion       : 0.00
% 2.46/1.31  Index Matching       : 0.00
% 2.46/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
