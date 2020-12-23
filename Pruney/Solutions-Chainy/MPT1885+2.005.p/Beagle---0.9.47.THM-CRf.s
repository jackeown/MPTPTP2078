%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:20 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 176 expanded)
%              Number of leaves         :   26 (  73 expanded)
%              Depth                    :   13
%              Number of atoms          :  136 ( 656 expanded)
%              Number of equality atoms :   19 (  75 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_tex_2 > v3_tex_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ ( v3_tex_2(B,A)
                & ! [C] :
                    ( ( ~ v2_struct_0(C)
                      & v1_pre_topc(C)
                      & m1_pre_topc(C,A) )
                   => ~ ( v4_tex_2(C,A)
                        & B = u1_struct_0(C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_tex_2)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v2_struct_0(A)
        & l1_struct_0(A) )
     => v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_74,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v4_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tex_2)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(c_6,plain,(
    ! [A_3] :
      ( l1_struct_0(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_30,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_46,plain,(
    ! [A_33,B_34] :
      ( u1_struct_0(k1_pre_topc(A_33,B_34)) = B_34
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_49,plain,
    ( u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3'
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_46])).

tff(c_52,plain,(
    u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_49])).

tff(c_10,plain,(
    ! [A_7] :
      ( v1_xboole_0(u1_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | ~ v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_62,plain,
    ( v1_xboole_0('#skF_3')
    | ~ l1_struct_0(k1_pre_topc('#skF_2','#skF_3'))
    | ~ v2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_10])).

tff(c_65,plain,
    ( ~ l1_struct_0(k1_pre_topc('#skF_2','#skF_3'))
    | ~ v2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_62])).

tff(c_67,plain,(
    ~ v2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_39,plain,(
    ! [A_31,B_32] :
      ( v1_pre_topc(k1_pre_topc(A_31,B_32))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_42,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_39])).

tff(c_45,plain,(
    v1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_42])).

tff(c_68,plain,(
    ! [A_35,B_36] :
      ( m1_pre_topc(k1_pre_topc(A_35,B_36),A_35)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_72,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_68])).

tff(c_75,plain,(
    m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_72])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_24,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_86,plain,(
    ! [B_40,A_41] :
      ( u1_struct_0(B_40) = '#skF_1'(A_41,B_40)
      | v4_tex_2(B_40,A_41)
      | ~ m1_pre_topc(B_40,A_41)
      | ~ l1_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    ! [C_25] :
      ( u1_struct_0(C_25) != '#skF_3'
      | ~ v4_tex_2(C_25,'#skF_2')
      | ~ m1_pre_topc(C_25,'#skF_2')
      | ~ v1_pre_topc(C_25)
      | v2_struct_0(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_90,plain,(
    ! [B_40] :
      ( u1_struct_0(B_40) != '#skF_3'
      | ~ v1_pre_topc(B_40)
      | v2_struct_0(B_40)
      | u1_struct_0(B_40) = '#skF_1'('#skF_2',B_40)
      | ~ m1_pre_topc(B_40,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_86,c_22])).

tff(c_93,plain,(
    ! [B_40] :
      ( u1_struct_0(B_40) != '#skF_3'
      | ~ v1_pre_topc(B_40)
      | v2_struct_0(B_40)
      | u1_struct_0(B_40) = '#skF_1'('#skF_2',B_40)
      | ~ m1_pre_topc(B_40,'#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_90])).

tff(c_95,plain,(
    ! [B_42] :
      ( u1_struct_0(B_42) != '#skF_3'
      | ~ v1_pre_topc(B_42)
      | v2_struct_0(B_42)
      | u1_struct_0(B_42) = '#skF_1'('#skF_2',B_42)
      | ~ m1_pre_topc(B_42,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_93])).

tff(c_98,plain,
    ( u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) != '#skF_3'
    | ~ v1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | v2_struct_0(k1_pre_topc('#skF_2','#skF_3'))
    | u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_75,c_95])).

tff(c_101,plain,
    ( v2_struct_0(k1_pre_topc('#skF_2','#skF_3'))
    | '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_45,c_52,c_98])).

tff(c_102,plain,(
    '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_101])).

tff(c_16,plain,(
    ! [A_11,B_17] :
      ( ~ v3_tex_2('#skF_1'(A_11,B_17),A_11)
      | v4_tex_2(B_17,A_11)
      | ~ m1_pre_topc(B_17,A_11)
      | ~ l1_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_106,plain,
    ( ~ v3_tex_2('#skF_3','#skF_2')
    | v4_tex_2(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_16])).

tff(c_110,plain,
    ( v4_tex_2(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_75,c_24,c_106])).

tff(c_111,plain,(
    v4_tex_2(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_110])).

tff(c_115,plain,
    ( u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) != '#skF_3'
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ v1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | v2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_111,c_22])).

tff(c_118,plain,(
    v2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_75,c_52,c_115])).

tff(c_120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_118])).

tff(c_121,plain,(
    ~ l1_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_134,plain,(
    ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_121])).

tff(c_123,plain,(
    ! [A_43,B_44] :
      ( m1_pre_topc(k1_pre_topc(A_43,B_44),A_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_127,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_123])).

tff(c_130,plain,(
    m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_127])).

tff(c_8,plain,(
    ! [B_6,A_4] :
      ( l1_pre_topc(B_6)
      | ~ m1_pre_topc(B_6,A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_137,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_130,c_8])).

tff(c_140,plain,(
    l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_137])).

tff(c_142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:27 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.23  
% 2.04/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.23  %$ v4_tex_2 > v3_tex_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.04/1.23  
% 2.04/1.23  %Foreground sorts:
% 2.04/1.23  
% 2.04/1.23  
% 2.04/1.23  %Background operators:
% 2.04/1.23  
% 2.04/1.23  
% 2.04/1.23  %Foreground operators:
% 2.04/1.23  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.04/1.23  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 2.04/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.23  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 2.04/1.23  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.04/1.23  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.04/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.23  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.04/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.23  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.04/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.23  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.04/1.23  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.04/1.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.04/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.04/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.04/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.23  
% 2.04/1.25  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.04/1.25  tff(f_104, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v3_tex_2(B, A) & (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ~(v4_tex_2(C, A) & (B = u1_struct_0(C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_tex_2)).
% 2.04/1.25  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 2.04/1.25  tff(f_50, axiom, (![A]: ((v2_struct_0(A) & l1_struct_0(A)) => v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_struct_0)).
% 2.04/1.25  tff(f_33, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 2.04/1.25  tff(f_74, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (v4_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_tex_2)).
% 2.04/1.25  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.04/1.25  tff(c_6, plain, (![A_3]: (l1_struct_0(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.04/1.25  tff(c_28, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.04/1.25  tff(c_30, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.04/1.25  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.04/1.25  tff(c_46, plain, (![A_33, B_34]: (u1_struct_0(k1_pre_topc(A_33, B_34))=B_34 | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.04/1.25  tff(c_49, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3' | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_46])).
% 2.04/1.25  tff(c_52, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_49])).
% 2.04/1.25  tff(c_10, plain, (![A_7]: (v1_xboole_0(u1_struct_0(A_7)) | ~l1_struct_0(A_7) | ~v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.04/1.25  tff(c_62, plain, (v1_xboole_0('#skF_3') | ~l1_struct_0(k1_pre_topc('#skF_2', '#skF_3')) | ~v2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_10])).
% 2.04/1.25  tff(c_65, plain, (~l1_struct_0(k1_pre_topc('#skF_2', '#skF_3')) | ~v2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_28, c_62])).
% 2.04/1.25  tff(c_67, plain, (~v2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_65])).
% 2.04/1.25  tff(c_39, plain, (![A_31, B_32]: (v1_pre_topc(k1_pre_topc(A_31, B_32)) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.04/1.25  tff(c_42, plain, (v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_39])).
% 2.04/1.25  tff(c_45, plain, (v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_42])).
% 2.04/1.25  tff(c_68, plain, (![A_35, B_36]: (m1_pre_topc(k1_pre_topc(A_35, B_36), A_35) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.04/1.25  tff(c_72, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_68])).
% 2.04/1.25  tff(c_75, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_72])).
% 2.04/1.25  tff(c_34, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.04/1.25  tff(c_24, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.04/1.25  tff(c_86, plain, (![B_40, A_41]: (u1_struct_0(B_40)='#skF_1'(A_41, B_40) | v4_tex_2(B_40, A_41) | ~m1_pre_topc(B_40, A_41) | ~l1_pre_topc(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.04/1.25  tff(c_22, plain, (![C_25]: (u1_struct_0(C_25)!='#skF_3' | ~v4_tex_2(C_25, '#skF_2') | ~m1_pre_topc(C_25, '#skF_2') | ~v1_pre_topc(C_25) | v2_struct_0(C_25))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.04/1.25  tff(c_90, plain, (![B_40]: (u1_struct_0(B_40)!='#skF_3' | ~v1_pre_topc(B_40) | v2_struct_0(B_40) | u1_struct_0(B_40)='#skF_1'('#skF_2', B_40) | ~m1_pre_topc(B_40, '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_86, c_22])).
% 2.04/1.25  tff(c_93, plain, (![B_40]: (u1_struct_0(B_40)!='#skF_3' | ~v1_pre_topc(B_40) | v2_struct_0(B_40) | u1_struct_0(B_40)='#skF_1'('#skF_2', B_40) | ~m1_pre_topc(B_40, '#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_90])).
% 2.04/1.25  tff(c_95, plain, (![B_42]: (u1_struct_0(B_42)!='#skF_3' | ~v1_pre_topc(B_42) | v2_struct_0(B_42) | u1_struct_0(B_42)='#skF_1'('#skF_2', B_42) | ~m1_pre_topc(B_42, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_34, c_93])).
% 2.04/1.25  tff(c_98, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))!='#skF_3' | ~v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | v2_struct_0(k1_pre_topc('#skF_2', '#skF_3')) | u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_75, c_95])).
% 2.04/1.25  tff(c_101, plain, (v2_struct_0(k1_pre_topc('#skF_2', '#skF_3')) | '#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_45, c_52, c_98])).
% 2.04/1.25  tff(c_102, plain, ('#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_67, c_101])).
% 2.04/1.25  tff(c_16, plain, (![A_11, B_17]: (~v3_tex_2('#skF_1'(A_11, B_17), A_11) | v4_tex_2(B_17, A_11) | ~m1_pre_topc(B_17, A_11) | ~l1_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.04/1.25  tff(c_106, plain, (~v3_tex_2('#skF_3', '#skF_2') | v4_tex_2(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_102, c_16])).
% 2.04/1.25  tff(c_110, plain, (v4_tex_2(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_75, c_24, c_106])).
% 2.04/1.25  tff(c_111, plain, (v4_tex_2(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_34, c_110])).
% 2.04/1.25  tff(c_115, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))!='#skF_3' | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | v2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_111, c_22])).
% 2.04/1.25  tff(c_118, plain, (v2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_75, c_52, c_115])).
% 2.04/1.25  tff(c_120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_118])).
% 2.04/1.25  tff(c_121, plain, (~l1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_65])).
% 2.04/1.25  tff(c_134, plain, (~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_6, c_121])).
% 2.04/1.25  tff(c_123, plain, (![A_43, B_44]: (m1_pre_topc(k1_pre_topc(A_43, B_44), A_43) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.04/1.25  tff(c_127, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_123])).
% 2.04/1.25  tff(c_130, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_127])).
% 2.04/1.25  tff(c_8, plain, (![B_6, A_4]: (l1_pre_topc(B_6) | ~m1_pre_topc(B_6, A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.04/1.25  tff(c_137, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_130, c_8])).
% 2.04/1.25  tff(c_140, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_137])).
% 2.04/1.25  tff(c_142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_140])).
% 2.04/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.25  
% 2.04/1.25  Inference rules
% 2.04/1.25  ----------------------
% 2.04/1.25  #Ref     : 0
% 2.04/1.25  #Sup     : 20
% 2.04/1.25  #Fact    : 0
% 2.04/1.25  #Define  : 0
% 2.04/1.25  #Split   : 1
% 2.04/1.25  #Chain   : 0
% 2.04/1.25  #Close   : 0
% 2.04/1.25  
% 2.04/1.25  Ordering : KBO
% 2.04/1.25  
% 2.04/1.25  Simplification rules
% 2.04/1.25  ----------------------
% 2.04/1.25  #Subsume      : 0
% 2.04/1.25  #Demod        : 17
% 2.04/1.25  #Tautology    : 4
% 2.04/1.25  #SimpNegUnit  : 6
% 2.04/1.25  #BackRed      : 0
% 2.04/1.25  
% 2.04/1.25  #Partial instantiations: 0
% 2.04/1.25  #Strategies tried      : 1
% 2.04/1.25  
% 2.04/1.25  Timing (in seconds)
% 2.04/1.25  ----------------------
% 2.17/1.25  Preprocessing        : 0.29
% 2.17/1.25  Parsing              : 0.15
% 2.17/1.25  CNF conversion       : 0.02
% 2.17/1.25  Main loop            : 0.14
% 2.17/1.25  Inferencing          : 0.05
% 2.17/1.25  Reduction            : 0.04
% 2.17/1.25  Demodulation         : 0.03
% 2.17/1.25  BG Simplification    : 0.01
% 2.17/1.25  Subsumption          : 0.02
% 2.17/1.25  Abstraction          : 0.01
% 2.17/1.25  MUC search           : 0.00
% 2.17/1.25  Cooper               : 0.00
% 2.17/1.25  Total                : 0.46
% 2.17/1.25  Index Insertion      : 0.00
% 2.17/1.25  Index Deletion       : 0.00
% 2.17/1.25  Index Matching       : 0.00
% 2.17/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
