%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:47 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 190 expanded)
%              Number of leaves         :   34 (  81 expanded)
%              Depth                    :   13
%              Number of atoms          :  163 ( 733 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_waybel_0 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_waybel_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_3

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

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_131,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_orders_2(B)
              & v7_waybel_0(B)
              & l1_waybel_0(B,A) )
           => r1_waybel_0(A,B,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v1_zfmisc_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc20_struct_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_92,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_waybel_0)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A)
        & m1_subset_1(C,u1_struct_0(B)) )
     => m1_subset_1(k2_waybel_0(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_waybel_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_51,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_44,plain,(
    l1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_36,plain,(
    l1_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_56,plain,(
    ! [B_80,A_81] :
      ( l1_orders_2(B_80)
      | ~ l1_waybel_0(B_80,A_81)
      | ~ l1_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_59,plain,
    ( l1_orders_2('#skF_6')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_56])).

tff(c_62,plain,(
    l1_orders_2('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_59])).

tff(c_18,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_11] :
      ( m1_subset_1('#skF_2'(A_11),k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_struct_0(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_70,plain,(
    ! [A_86,C_87,B_88] :
      ( m1_subset_1(A_86,C_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(C_87))
      | ~ r2_hidden(A_86,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_74,plain,(
    ! [A_89,A_90] :
      ( m1_subset_1(A_89,u1_struct_0(A_90))
      | ~ r2_hidden(A_89,'#skF_2'(A_90))
      | ~ l1_struct_0(A_90)
      | v2_struct_0(A_90) ) ),
    inference(resolution,[status(thm)],[c_16,c_70])).

tff(c_84,plain,(
    ! [A_90] :
      ( m1_subset_1('#skF_1'('#skF_2'(A_90)),u1_struct_0(A_90))
      | ~ l1_struct_0(A_90)
      | v2_struct_0(A_90)
      | v1_xboole_0('#skF_2'(A_90)) ) ),
    inference(resolution,[status(thm)],[c_4,c_74])).

tff(c_28,plain,(
    ! [A_14,B_42,C_56,D_63] :
      ( m1_subset_1('#skF_3'(A_14,B_42,C_56,D_63),u1_struct_0(B_42))
      | r1_waybel_0(A_14,B_42,C_56)
      | ~ m1_subset_1(D_63,u1_struct_0(B_42))
      | ~ l1_waybel_0(B_42,A_14)
      | v2_struct_0(B_42)
      | ~ l1_struct_0(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    ! [A_67,B_68,C_69] :
      ( m1_subset_1(k2_waybel_0(A_67,B_68,C_69),u1_struct_0(A_67))
      | ~ m1_subset_1(C_69,u1_struct_0(B_68))
      | ~ l1_waybel_0(B_68,A_67)
      | v2_struct_0(B_68)
      | ~ l1_struct_0(A_67)
      | v2_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_91,plain,(
    ! [A_108,B_109,C_110,D_111] :
      ( ~ r2_hidden(k2_waybel_0(A_108,B_109,'#skF_3'(A_108,B_109,C_110,D_111)),C_110)
      | r1_waybel_0(A_108,B_109,C_110)
      | ~ m1_subset_1(D_111,u1_struct_0(B_109))
      | ~ l1_waybel_0(B_109,A_108)
      | v2_struct_0(B_109)
      | ~ l1_struct_0(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_97,plain,(
    ! [A_112,B_113,B_114,D_115] :
      ( r1_waybel_0(A_112,B_113,B_114)
      | ~ m1_subset_1(D_115,u1_struct_0(B_113))
      | ~ l1_waybel_0(B_113,A_112)
      | v2_struct_0(B_113)
      | ~ l1_struct_0(A_112)
      | v2_struct_0(A_112)
      | v1_xboole_0(B_114)
      | ~ m1_subset_1(k2_waybel_0(A_112,B_113,'#skF_3'(A_112,B_113,B_114,D_115)),B_114) ) ),
    inference(resolution,[status(thm)],[c_6,c_91])).

tff(c_114,plain,(
    ! [A_120,B_121,D_122] :
      ( r1_waybel_0(A_120,B_121,u1_struct_0(A_120))
      | ~ m1_subset_1(D_122,u1_struct_0(B_121))
      | v1_xboole_0(u1_struct_0(A_120))
      | ~ m1_subset_1('#skF_3'(A_120,B_121,u1_struct_0(A_120),D_122),u1_struct_0(B_121))
      | ~ l1_waybel_0(B_121,A_120)
      | v2_struct_0(B_121)
      | ~ l1_struct_0(A_120)
      | v2_struct_0(A_120) ) ),
    inference(resolution,[status(thm)],[c_30,c_97])).

tff(c_125,plain,(
    ! [A_123,B_124,D_125] :
      ( v1_xboole_0(u1_struct_0(A_123))
      | r1_waybel_0(A_123,B_124,u1_struct_0(A_123))
      | ~ m1_subset_1(D_125,u1_struct_0(B_124))
      | ~ l1_waybel_0(B_124,A_123)
      | v2_struct_0(B_124)
      | ~ l1_struct_0(A_123)
      | v2_struct_0(A_123) ) ),
    inference(resolution,[status(thm)],[c_28,c_114])).

tff(c_141,plain,(
    ! [A_126,A_127] :
      ( v1_xboole_0(u1_struct_0(A_126))
      | r1_waybel_0(A_126,A_127,u1_struct_0(A_126))
      | ~ l1_waybel_0(A_127,A_126)
      | ~ l1_struct_0(A_126)
      | v2_struct_0(A_126)
      | ~ l1_struct_0(A_127)
      | v2_struct_0(A_127)
      | v1_xboole_0('#skF_2'(A_127)) ) ),
    inference(resolution,[status(thm)],[c_84,c_125])).

tff(c_34,plain,(
    ~ r1_waybel_0('#skF_5','#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_144,plain,
    ( v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6')
    | v1_xboole_0('#skF_2'('#skF_6')) ),
    inference(resolution,[status(thm)],[c_141,c_34])).

tff(c_147,plain,
    ( v1_xboole_0(u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6')
    | v1_xboole_0('#skF_2'('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_144])).

tff(c_148,plain,
    ( v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ l1_struct_0('#skF_6')
    | v1_xboole_0('#skF_2'('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_46,c_147])).

tff(c_149,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_152,plain,(
    ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_18,c_149])).

tff(c_156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_152])).

tff(c_158,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_157,plain,
    ( v1_xboole_0('#skF_2'('#skF_6'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_159,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_10,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_177,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_159,c_10])).

tff(c_180,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_177])).

tff(c_182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_180])).

tff(c_183,plain,(
    v1_xboole_0('#skF_2'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_14,plain,(
    ! [A_11] :
      ( ~ v1_xboole_0('#skF_2'(A_11))
      | ~ l1_struct_0(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_187,plain,
    ( ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_183,c_14])).

tff(c_190,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_187])).

tff(c_192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:07:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.34  
% 2.23/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.34  %$ r1_waybel_0 > r1_orders_2 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_waybel_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_3
% 2.23/1.34  
% 2.23/1.34  %Foreground sorts:
% 2.23/1.34  
% 2.23/1.34  
% 2.23/1.34  %Background operators:
% 2.23/1.34  
% 2.23/1.34  
% 2.23/1.34  %Foreground operators:
% 2.23/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.23/1.34  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.23/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.23/1.34  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.23/1.34  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.23/1.34  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.23/1.34  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.23/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.23/1.34  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.23/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.23/1.34  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.23/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.34  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.23/1.34  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.23/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.34  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.23/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.34  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.23/1.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.23/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.23/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.34  
% 2.51/1.36  tff(f_131, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_yellow_6)).
% 2.51/1.36  tff(f_113, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 2.51/1.36  tff(f_68, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.51/1.36  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.51/1.36  tff(f_64, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v1_zfmisc_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc20_struct_0)).
% 2.51/1.36  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.51/1.36  tff(f_92, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) <=> (?[D]: (m1_subset_1(D, u1_struct_0(B)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r1_orders_2(B, D, E) => r2_hidden(k2_waybel_0(A, B, E), C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_waybel_0)).
% 2.51/1.36  tff(f_106, axiom, (![A, B, C]: (((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & l1_waybel_0(B, A)) & m1_subset_1(C, u1_struct_0(B))) => m1_subset_1(k2_waybel_0(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_waybel_0)).
% 2.51/1.36  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.51/1.36  tff(f_51, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.51/1.36  tff(c_42, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.51/1.36  tff(c_44, plain, (l1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.51/1.36  tff(c_36, plain, (l1_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.51/1.36  tff(c_56, plain, (![B_80, A_81]: (l1_orders_2(B_80) | ~l1_waybel_0(B_80, A_81) | ~l1_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.51/1.36  tff(c_59, plain, (l1_orders_2('#skF_6') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_36, c_56])).
% 2.51/1.36  tff(c_62, plain, (l1_orders_2('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_59])).
% 2.51/1.36  tff(c_18, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_orders_2(A_13))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.51/1.36  tff(c_46, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.51/1.36  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.51/1.36  tff(c_16, plain, (![A_11]: (m1_subset_1('#skF_2'(A_11), k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_struct_0(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.51/1.36  tff(c_70, plain, (![A_86, C_87, B_88]: (m1_subset_1(A_86, C_87) | ~m1_subset_1(B_88, k1_zfmisc_1(C_87)) | ~r2_hidden(A_86, B_88))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.51/1.36  tff(c_74, plain, (![A_89, A_90]: (m1_subset_1(A_89, u1_struct_0(A_90)) | ~r2_hidden(A_89, '#skF_2'(A_90)) | ~l1_struct_0(A_90) | v2_struct_0(A_90))), inference(resolution, [status(thm)], [c_16, c_70])).
% 2.51/1.36  tff(c_84, plain, (![A_90]: (m1_subset_1('#skF_1'('#skF_2'(A_90)), u1_struct_0(A_90)) | ~l1_struct_0(A_90) | v2_struct_0(A_90) | v1_xboole_0('#skF_2'(A_90)))), inference(resolution, [status(thm)], [c_4, c_74])).
% 2.51/1.36  tff(c_28, plain, (![A_14, B_42, C_56, D_63]: (m1_subset_1('#skF_3'(A_14, B_42, C_56, D_63), u1_struct_0(B_42)) | r1_waybel_0(A_14, B_42, C_56) | ~m1_subset_1(D_63, u1_struct_0(B_42)) | ~l1_waybel_0(B_42, A_14) | v2_struct_0(B_42) | ~l1_struct_0(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.51/1.36  tff(c_30, plain, (![A_67, B_68, C_69]: (m1_subset_1(k2_waybel_0(A_67, B_68, C_69), u1_struct_0(A_67)) | ~m1_subset_1(C_69, u1_struct_0(B_68)) | ~l1_waybel_0(B_68, A_67) | v2_struct_0(B_68) | ~l1_struct_0(A_67) | v2_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.51/1.36  tff(c_6, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.51/1.36  tff(c_91, plain, (![A_108, B_109, C_110, D_111]: (~r2_hidden(k2_waybel_0(A_108, B_109, '#skF_3'(A_108, B_109, C_110, D_111)), C_110) | r1_waybel_0(A_108, B_109, C_110) | ~m1_subset_1(D_111, u1_struct_0(B_109)) | ~l1_waybel_0(B_109, A_108) | v2_struct_0(B_109) | ~l1_struct_0(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.51/1.36  tff(c_97, plain, (![A_112, B_113, B_114, D_115]: (r1_waybel_0(A_112, B_113, B_114) | ~m1_subset_1(D_115, u1_struct_0(B_113)) | ~l1_waybel_0(B_113, A_112) | v2_struct_0(B_113) | ~l1_struct_0(A_112) | v2_struct_0(A_112) | v1_xboole_0(B_114) | ~m1_subset_1(k2_waybel_0(A_112, B_113, '#skF_3'(A_112, B_113, B_114, D_115)), B_114))), inference(resolution, [status(thm)], [c_6, c_91])).
% 2.51/1.36  tff(c_114, plain, (![A_120, B_121, D_122]: (r1_waybel_0(A_120, B_121, u1_struct_0(A_120)) | ~m1_subset_1(D_122, u1_struct_0(B_121)) | v1_xboole_0(u1_struct_0(A_120)) | ~m1_subset_1('#skF_3'(A_120, B_121, u1_struct_0(A_120), D_122), u1_struct_0(B_121)) | ~l1_waybel_0(B_121, A_120) | v2_struct_0(B_121) | ~l1_struct_0(A_120) | v2_struct_0(A_120))), inference(resolution, [status(thm)], [c_30, c_97])).
% 2.51/1.36  tff(c_125, plain, (![A_123, B_124, D_125]: (v1_xboole_0(u1_struct_0(A_123)) | r1_waybel_0(A_123, B_124, u1_struct_0(A_123)) | ~m1_subset_1(D_125, u1_struct_0(B_124)) | ~l1_waybel_0(B_124, A_123) | v2_struct_0(B_124) | ~l1_struct_0(A_123) | v2_struct_0(A_123))), inference(resolution, [status(thm)], [c_28, c_114])).
% 2.51/1.36  tff(c_141, plain, (![A_126, A_127]: (v1_xboole_0(u1_struct_0(A_126)) | r1_waybel_0(A_126, A_127, u1_struct_0(A_126)) | ~l1_waybel_0(A_127, A_126) | ~l1_struct_0(A_126) | v2_struct_0(A_126) | ~l1_struct_0(A_127) | v2_struct_0(A_127) | v1_xboole_0('#skF_2'(A_127)))), inference(resolution, [status(thm)], [c_84, c_125])).
% 2.51/1.36  tff(c_34, plain, (~r1_waybel_0('#skF_5', '#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.51/1.36  tff(c_144, plain, (v1_xboole_0(u1_struct_0('#skF_5')) | ~l1_waybel_0('#skF_6', '#skF_5') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6') | v1_xboole_0('#skF_2'('#skF_6'))), inference(resolution, [status(thm)], [c_141, c_34])).
% 2.51/1.36  tff(c_147, plain, (v1_xboole_0(u1_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6') | v1_xboole_0('#skF_2'('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_144])).
% 2.51/1.36  tff(c_148, plain, (v1_xboole_0(u1_struct_0('#skF_5')) | ~l1_struct_0('#skF_6') | v1_xboole_0('#skF_2'('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_42, c_46, c_147])).
% 2.51/1.36  tff(c_149, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_148])).
% 2.51/1.36  tff(c_152, plain, (~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_18, c_149])).
% 2.51/1.36  tff(c_156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_152])).
% 2.51/1.36  tff(c_158, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_148])).
% 2.51/1.36  tff(c_157, plain, (v1_xboole_0('#skF_2'('#skF_6')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_148])).
% 2.51/1.36  tff(c_159, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_157])).
% 2.51/1.36  tff(c_10, plain, (![A_10]: (~v1_xboole_0(u1_struct_0(A_10)) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.51/1.36  tff(c_177, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_159, c_10])).
% 2.51/1.36  tff(c_180, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_177])).
% 2.51/1.36  tff(c_182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_180])).
% 2.51/1.36  tff(c_183, plain, (v1_xboole_0('#skF_2'('#skF_6'))), inference(splitRight, [status(thm)], [c_157])).
% 2.51/1.36  tff(c_14, plain, (![A_11]: (~v1_xboole_0('#skF_2'(A_11)) | ~l1_struct_0(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.51/1.36  tff(c_187, plain, (~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_183, c_14])).
% 2.51/1.36  tff(c_190, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_187])).
% 2.51/1.36  tff(c_192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_190])).
% 2.51/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.36  
% 2.51/1.36  Inference rules
% 2.51/1.36  ----------------------
% 2.51/1.36  #Ref     : 0
% 2.51/1.36  #Sup     : 24
% 2.51/1.36  #Fact    : 0
% 2.51/1.36  #Define  : 0
% 2.51/1.36  #Split   : 2
% 2.51/1.36  #Chain   : 0
% 2.51/1.36  #Close   : 0
% 2.51/1.36  
% 2.51/1.36  Ordering : KBO
% 2.51/1.36  
% 2.51/1.36  Simplification rules
% 2.51/1.36  ----------------------
% 2.51/1.36  #Subsume      : 2
% 2.51/1.36  #Demod        : 6
% 2.51/1.36  #Tautology    : 3
% 2.51/1.36  #SimpNegUnit  : 3
% 2.51/1.36  #BackRed      : 0
% 2.51/1.36  
% 2.51/1.36  #Partial instantiations: 0
% 2.51/1.36  #Strategies tried      : 1
% 2.51/1.36  
% 2.51/1.36  Timing (in seconds)
% 2.51/1.36  ----------------------
% 2.51/1.36  Preprocessing        : 0.31
% 2.51/1.36  Parsing              : 0.18
% 2.51/1.36  CNF conversion       : 0.03
% 2.51/1.36  Main loop            : 0.21
% 2.51/1.36  Inferencing          : 0.09
% 2.51/1.36  Reduction            : 0.05
% 2.51/1.36  Demodulation         : 0.03
% 2.51/1.36  BG Simplification    : 0.01
% 2.51/1.36  Subsumption          : 0.04
% 2.51/1.36  Abstraction          : 0.01
% 2.51/1.36  MUC search           : 0.00
% 2.51/1.36  Cooper               : 0.00
% 2.51/1.36  Total                : 0.56
% 2.51/1.36  Index Insertion      : 0.00
% 2.51/1.37  Index Deletion       : 0.00
% 2.51/1.37  Index Matching       : 0.00
% 2.51/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
