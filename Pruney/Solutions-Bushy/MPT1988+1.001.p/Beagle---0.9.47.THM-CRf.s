%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1988+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:45 EST 2020

% Result     : Theorem 9.59s
% Output     : CNFRefutation 9.59s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 383 expanded)
%              Number of leaves         :   39 ( 156 expanded)
%              Depth                    :   24
%              Number of atoms          :  560 (2568 expanded)
%              Number of equality atoms :   10 (  50 expanded)
%              Maximal formula depth    :   30 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v5_waybel_6 > v1_waybel_7 > v1_waybel_0 > v12_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_lattice3 > l1_orders_2 > k12_lattice3 > k11_lattice3 > k5_waybel_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_waybel_7,type,(
    v1_waybel_7: ( $i * $i ) > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v5_waybel_6,type,(
    v5_waybel_6: ( $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff(v12_waybel_0,type,(
    v12_waybel_0: ( $i * $i ) > $o )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k5_waybel_0,type,(
    k5_waybel_0: ( $i * $i ) > $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(v1_waybel_0,type,(
    v1_waybel_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_180,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v5_waybel_6(B,A)
             => v1_waybel_7(k5_waybel_0(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_waybel_7)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v5_waybel_6(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ~ ( r1_orders_2(A,k11_lattice3(A,C,D),B)
                        & ~ r1_orders_2(A,C,B)
                        & ~ r1_orders_2(A,D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_waybel_6)).

tff(f_139,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v4_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => v12_waybel_0(k5_waybel_0(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_waybel_0)).

tff(f_127,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v1_xboole_0(k5_waybel_0(A,B))
        & v1_waybel_0(k5_waybel_0(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_waybel_0)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k5_waybel_0(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_waybel_0)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_waybel_0(B,A)
            & v12_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v1_waybel_7(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ~ ( r2_hidden(k12_lattice3(A,C,D),B)
                        & ~ r2_hidden(C,B)
                        & ~ r2_hidden(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_waybel_7)).

tff(f_160,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_154,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k5_waybel_0(A,B))
              <=> r1_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_waybel_0)).

tff(c_50,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_52,plain,(
    v2_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_26,plain,(
    ! [A_27,B_41] :
      ( m1_subset_1('#skF_3'(A_27,B_41),u1_struct_0(A_27))
      | v5_waybel_6(B_41,A_27)
      | ~ m1_subset_1(B_41,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_56,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_102,plain,(
    ! [A_105,B_106,C_107] :
      ( k12_lattice3(A_105,B_106,C_107) = k11_lattice3(A_105,B_106,C_107)
      | ~ m1_subset_1(C_107,u1_struct_0(A_105))
      | ~ m1_subset_1(B_106,u1_struct_0(A_105))
      | ~ l1_orders_2(A_105)
      | ~ v2_lattice3(A_105)
      | ~ v5_orders_2(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_108,plain,(
    ! [B_106] :
      ( k12_lattice3('#skF_5',B_106,'#skF_6') = k11_lattice3('#skF_5',B_106,'#skF_6')
      | ~ m1_subset_1(B_106,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v2_lattice3('#skF_5')
      | ~ v5_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_102])).

tff(c_114,plain,(
    ! [B_108] :
      ( k12_lattice3('#skF_5',B_108,'#skF_6') = k11_lattice3('#skF_5',B_108,'#skF_6')
      | ~ m1_subset_1(B_108,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_50,c_108])).

tff(c_118,plain,(
    ! [B_41] :
      ( k12_lattice3('#skF_5','#skF_3'('#skF_5',B_41),'#skF_6') = k11_lattice3('#skF_5','#skF_3'('#skF_5',B_41),'#skF_6')
      | v5_waybel_6(B_41,'#skF_5')
      | ~ m1_subset_1(B_41,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26,c_114])).

tff(c_128,plain,(
    ! [B_41] :
      ( k12_lattice3('#skF_5','#skF_3'('#skF_5',B_41),'#skF_6') = k11_lattice3('#skF_5','#skF_3'('#skF_5',B_41),'#skF_6')
      | v5_waybel_6(B_41,'#skF_5')
      | ~ m1_subset_1(B_41,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_118])).

tff(c_137,plain,(
    v2_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v2_struct_0(A_1)
      | ~ v2_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_140,plain,
    ( ~ v2_lattice3('#skF_5')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_137,c_2])).

tff(c_144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_140])).

tff(c_146,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_58,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_30,plain,(
    ! [A_54,B_55] :
      ( v12_waybel_0(k5_waybel_0(A_54,B_55),A_54)
      | ~ m1_subset_1(B_55,u1_struct_0(A_54))
      | ~ l1_orders_2(A_54)
      | ~ v4_orders_2(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_60,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_32,plain,(
    ! [A_56,B_57] :
      ( v1_waybel_0(k5_waybel_0(A_56,B_57),A_56)
      | ~ m1_subset_1(B_57,u1_struct_0(A_56))
      | ~ l1_orders_2(A_56)
      | ~ v3_orders_2(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_63,plain,(
    ! [A_76,B_77] :
      ( ~ v1_xboole_0(k5_waybel_0(A_76,B_77))
      | ~ m1_subset_1(B_77,u1_struct_0(A_76))
      | ~ l1_orders_2(A_76)
      | ~ v3_orders_2(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_66,plain,
    ( ~ v1_xboole_0(k5_waybel_0('#skF_5','#skF_6'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_63])).

tff(c_69,plain,
    ( ~ v1_xboole_0(k5_waybel_0('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_66])).

tff(c_70,plain,(
    ~ v1_xboole_0(k5_waybel_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_46,plain,(
    v5_waybel_6('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_28,plain,(
    ! [A_52,B_53] :
      ( m1_subset_1(k5_waybel_0(A_52,B_53),k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ m1_subset_1(B_53,u1_struct_0(A_52))
      | ~ l1_orders_2(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_14,plain,(
    ! [A_2,B_16] :
      ( m1_subset_1('#skF_1'(A_2,B_16),u1_struct_0(A_2))
      | v1_waybel_7(B_16,A_2)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ v12_waybel_0(B_16,A_2)
      | ~ v1_waybel_0(B_16,A_2)
      | v1_xboole_0(B_16)
      | ~ l1_orders_2(A_2)
      | ~ v2_lattice3(A_2)
      | ~ v5_orders_2(A_2)
      | ~ v4_orders_2(A_2)
      | ~ v3_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,(
    ! [A_2,B_16] :
      ( m1_subset_1('#skF_2'(A_2,B_16),u1_struct_0(A_2))
      | v1_waybel_7(B_16,A_2)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ v12_waybel_0(B_16,A_2)
      | ~ v1_waybel_0(B_16,A_2)
      | v1_xboole_0(B_16)
      | ~ l1_orders_2(A_2)
      | ~ v2_lattice3(A_2)
      | ~ v5_orders_2(A_2)
      | ~ v4_orders_2(A_2)
      | ~ v3_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_412,plain,(
    ! [A_137,B_138] :
      ( m1_subset_1('#skF_2'(A_137,B_138),u1_struct_0(A_137))
      | v1_waybel_7(B_138,A_137)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(u1_struct_0(A_137)))
      | ~ v12_waybel_0(B_138,A_137)
      | ~ v1_waybel_0(B_138,A_137)
      | v1_xboole_0(B_138)
      | ~ l1_orders_2(A_137)
      | ~ v2_lattice3(A_137)
      | ~ v5_orders_2(A_137)
      | ~ v4_orders_2(A_137)
      | ~ v3_orders_2(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,(
    ! [A_58,B_59,C_60] :
      ( k12_lattice3(A_58,B_59,C_60) = k11_lattice3(A_58,B_59,C_60)
      | ~ m1_subset_1(C_60,u1_struct_0(A_58))
      | ~ m1_subset_1(B_59,u1_struct_0(A_58))
      | ~ l1_orders_2(A_58)
      | ~ v2_lattice3(A_58)
      | ~ v5_orders_2(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_701,plain,(
    ! [A_180,B_181,B_182] :
      ( k12_lattice3(A_180,B_181,'#skF_2'(A_180,B_182)) = k11_lattice3(A_180,B_181,'#skF_2'(A_180,B_182))
      | ~ m1_subset_1(B_181,u1_struct_0(A_180))
      | v1_waybel_7(B_182,A_180)
      | ~ m1_subset_1(B_182,k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ v12_waybel_0(B_182,A_180)
      | ~ v1_waybel_0(B_182,A_180)
      | v1_xboole_0(B_182)
      | ~ l1_orders_2(A_180)
      | ~ v2_lattice3(A_180)
      | ~ v5_orders_2(A_180)
      | ~ v4_orders_2(A_180)
      | ~ v3_orders_2(A_180) ) ),
    inference(resolution,[status(thm)],[c_412,c_36])).

tff(c_975,plain,(
    ! [A_257,B_258,B_259] :
      ( k12_lattice3(A_257,'#skF_1'(A_257,B_258),'#skF_2'(A_257,B_259)) = k11_lattice3(A_257,'#skF_1'(A_257,B_258),'#skF_2'(A_257,B_259))
      | v1_waybel_7(B_259,A_257)
      | ~ m1_subset_1(B_259,k1_zfmisc_1(u1_struct_0(A_257)))
      | ~ v12_waybel_0(B_259,A_257)
      | ~ v1_waybel_0(B_259,A_257)
      | v1_xboole_0(B_259)
      | v1_waybel_7(B_258,A_257)
      | ~ m1_subset_1(B_258,k1_zfmisc_1(u1_struct_0(A_257)))
      | ~ v12_waybel_0(B_258,A_257)
      | ~ v1_waybel_0(B_258,A_257)
      | v1_xboole_0(B_258)
      | ~ l1_orders_2(A_257)
      | ~ v2_lattice3(A_257)
      | ~ v5_orders_2(A_257)
      | ~ v4_orders_2(A_257)
      | ~ v3_orders_2(A_257) ) ),
    inference(resolution,[status(thm)],[c_14,c_701])).

tff(c_1301,plain,(
    ! [A_310,B_311,B_312] :
      ( k12_lattice3(A_310,'#skF_1'(A_310,B_311),'#skF_2'(A_310,k5_waybel_0(A_310,B_312))) = k11_lattice3(A_310,'#skF_1'(A_310,B_311),'#skF_2'(A_310,k5_waybel_0(A_310,B_312)))
      | v1_waybel_7(k5_waybel_0(A_310,B_312),A_310)
      | ~ v12_waybel_0(k5_waybel_0(A_310,B_312),A_310)
      | ~ v1_waybel_0(k5_waybel_0(A_310,B_312),A_310)
      | v1_xboole_0(k5_waybel_0(A_310,B_312))
      | v1_waybel_7(B_311,A_310)
      | ~ m1_subset_1(B_311,k1_zfmisc_1(u1_struct_0(A_310)))
      | ~ v12_waybel_0(B_311,A_310)
      | ~ v1_waybel_0(B_311,A_310)
      | v1_xboole_0(B_311)
      | ~ v2_lattice3(A_310)
      | ~ v5_orders_2(A_310)
      | ~ v4_orders_2(A_310)
      | ~ v3_orders_2(A_310)
      | ~ m1_subset_1(B_312,u1_struct_0(A_310))
      | ~ l1_orders_2(A_310)
      | v2_struct_0(A_310) ) ),
    inference(resolution,[status(thm)],[c_28,c_975])).

tff(c_10,plain,(
    ! [A_2,B_16] :
      ( r2_hidden(k12_lattice3(A_2,'#skF_1'(A_2,B_16),'#skF_2'(A_2,B_16)),B_16)
      | v1_waybel_7(B_16,A_2)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ v12_waybel_0(B_16,A_2)
      | ~ v1_waybel_0(B_16,A_2)
      | v1_xboole_0(B_16)
      | ~ l1_orders_2(A_2)
      | ~ v2_lattice3(A_2)
      | ~ v5_orders_2(A_2)
      | ~ v4_orders_2(A_2)
      | ~ v3_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1868,plain,(
    ! [A_546,B_547] :
      ( r2_hidden(k11_lattice3(A_546,'#skF_1'(A_546,k5_waybel_0(A_546,B_547)),'#skF_2'(A_546,k5_waybel_0(A_546,B_547))),k5_waybel_0(A_546,B_547))
      | v1_waybel_7(k5_waybel_0(A_546,B_547),A_546)
      | ~ m1_subset_1(k5_waybel_0(A_546,B_547),k1_zfmisc_1(u1_struct_0(A_546)))
      | ~ v12_waybel_0(k5_waybel_0(A_546,B_547),A_546)
      | ~ v1_waybel_0(k5_waybel_0(A_546,B_547),A_546)
      | v1_xboole_0(k5_waybel_0(A_546,B_547))
      | ~ l1_orders_2(A_546)
      | ~ v2_lattice3(A_546)
      | ~ v5_orders_2(A_546)
      | ~ v4_orders_2(A_546)
      | ~ v3_orders_2(A_546)
      | v1_waybel_7(k5_waybel_0(A_546,B_547),A_546)
      | ~ v12_waybel_0(k5_waybel_0(A_546,B_547),A_546)
      | ~ v1_waybel_0(k5_waybel_0(A_546,B_547),A_546)
      | v1_xboole_0(k5_waybel_0(A_546,B_547))
      | v1_waybel_7(k5_waybel_0(A_546,B_547),A_546)
      | ~ m1_subset_1(k5_waybel_0(A_546,B_547),k1_zfmisc_1(u1_struct_0(A_546)))
      | ~ v12_waybel_0(k5_waybel_0(A_546,B_547),A_546)
      | ~ v1_waybel_0(k5_waybel_0(A_546,B_547),A_546)
      | v1_xboole_0(k5_waybel_0(A_546,B_547))
      | ~ v2_lattice3(A_546)
      | ~ v5_orders_2(A_546)
      | ~ v4_orders_2(A_546)
      | ~ v3_orders_2(A_546)
      | ~ m1_subset_1(B_547,u1_struct_0(A_546))
      | ~ l1_orders_2(A_546)
      | v2_struct_0(A_546) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1301,c_10])).

tff(c_73,plain,(
    ! [A_82,B_83] :
      ( m1_subset_1(k5_waybel_0(A_82,B_83),k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ m1_subset_1(B_83,u1_struct_0(A_82))
      | ~ l1_orders_2(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_42,plain,(
    ! [A_68,C_70,B_69] :
      ( m1_subset_1(A_68,C_70)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(C_70))
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_76,plain,(
    ! [A_68,A_82,B_83] :
      ( m1_subset_1(A_68,u1_struct_0(A_82))
      | ~ r2_hidden(A_68,k5_waybel_0(A_82,B_83))
      | ~ m1_subset_1(B_83,u1_struct_0(A_82))
      | ~ l1_orders_2(A_82)
      | v2_struct_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_73,c_42])).

tff(c_1876,plain,(
    ! [A_546,B_547] :
      ( m1_subset_1(k11_lattice3(A_546,'#skF_1'(A_546,k5_waybel_0(A_546,B_547)),'#skF_2'(A_546,k5_waybel_0(A_546,B_547))),u1_struct_0(A_546))
      | v1_waybel_7(k5_waybel_0(A_546,B_547),A_546)
      | ~ m1_subset_1(k5_waybel_0(A_546,B_547),k1_zfmisc_1(u1_struct_0(A_546)))
      | ~ v12_waybel_0(k5_waybel_0(A_546,B_547),A_546)
      | ~ v1_waybel_0(k5_waybel_0(A_546,B_547),A_546)
      | v1_xboole_0(k5_waybel_0(A_546,B_547))
      | ~ v2_lattice3(A_546)
      | ~ v5_orders_2(A_546)
      | ~ v4_orders_2(A_546)
      | ~ v3_orders_2(A_546)
      | ~ m1_subset_1(B_547,u1_struct_0(A_546))
      | ~ l1_orders_2(A_546)
      | v2_struct_0(A_546) ) ),
    inference(resolution,[status(thm)],[c_1868,c_76])).

tff(c_40,plain,(
    ! [A_61,C_67,B_65] :
      ( r1_orders_2(A_61,C_67,B_65)
      | ~ r2_hidden(C_67,k5_waybel_0(A_61,B_65))
      | ~ m1_subset_1(C_67,u1_struct_0(A_61))
      | ~ m1_subset_1(B_65,u1_struct_0(A_61))
      | ~ l1_orders_2(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1962,plain,(
    ! [A_553,B_554] :
      ( r1_orders_2(A_553,k11_lattice3(A_553,'#skF_1'(A_553,k5_waybel_0(A_553,B_554)),'#skF_2'(A_553,k5_waybel_0(A_553,B_554))),B_554)
      | ~ m1_subset_1(k11_lattice3(A_553,'#skF_1'(A_553,k5_waybel_0(A_553,B_554)),'#skF_2'(A_553,k5_waybel_0(A_553,B_554))),u1_struct_0(A_553))
      | v1_waybel_7(k5_waybel_0(A_553,B_554),A_553)
      | ~ m1_subset_1(k5_waybel_0(A_553,B_554),k1_zfmisc_1(u1_struct_0(A_553)))
      | ~ v12_waybel_0(k5_waybel_0(A_553,B_554),A_553)
      | ~ v1_waybel_0(k5_waybel_0(A_553,B_554),A_553)
      | v1_xboole_0(k5_waybel_0(A_553,B_554))
      | ~ v2_lattice3(A_553)
      | ~ v5_orders_2(A_553)
      | ~ v4_orders_2(A_553)
      | ~ v3_orders_2(A_553)
      | ~ m1_subset_1(B_554,u1_struct_0(A_553))
      | ~ l1_orders_2(A_553)
      | v2_struct_0(A_553) ) ),
    inference(resolution,[status(thm)],[c_1868,c_40])).

tff(c_1966,plain,(
    ! [A_555,B_556] :
      ( r1_orders_2(A_555,k11_lattice3(A_555,'#skF_1'(A_555,k5_waybel_0(A_555,B_556)),'#skF_2'(A_555,k5_waybel_0(A_555,B_556))),B_556)
      | v1_waybel_7(k5_waybel_0(A_555,B_556),A_555)
      | ~ m1_subset_1(k5_waybel_0(A_555,B_556),k1_zfmisc_1(u1_struct_0(A_555)))
      | ~ v12_waybel_0(k5_waybel_0(A_555,B_556),A_555)
      | ~ v1_waybel_0(k5_waybel_0(A_555,B_556),A_555)
      | v1_xboole_0(k5_waybel_0(A_555,B_556))
      | ~ v2_lattice3(A_555)
      | ~ v5_orders_2(A_555)
      | ~ v4_orders_2(A_555)
      | ~ v3_orders_2(A_555)
      | ~ m1_subset_1(B_556,u1_struct_0(A_555))
      | ~ l1_orders_2(A_555)
      | v2_struct_0(A_555) ) ),
    inference(resolution,[status(thm)],[c_1876,c_1962])).

tff(c_16,plain,(
    ! [A_27,D_50,B_41,C_48] :
      ( r1_orders_2(A_27,D_50,B_41)
      | r1_orders_2(A_27,C_48,B_41)
      | ~ r1_orders_2(A_27,k11_lattice3(A_27,C_48,D_50),B_41)
      | ~ m1_subset_1(D_50,u1_struct_0(A_27))
      | ~ m1_subset_1(C_48,u1_struct_0(A_27))
      | ~ v5_waybel_6(B_41,A_27)
      | ~ m1_subset_1(B_41,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1984,plain,(
    ! [A_560,B_561] :
      ( r1_orders_2(A_560,'#skF_2'(A_560,k5_waybel_0(A_560,B_561)),B_561)
      | r1_orders_2(A_560,'#skF_1'(A_560,k5_waybel_0(A_560,B_561)),B_561)
      | ~ m1_subset_1('#skF_2'(A_560,k5_waybel_0(A_560,B_561)),u1_struct_0(A_560))
      | ~ m1_subset_1('#skF_1'(A_560,k5_waybel_0(A_560,B_561)),u1_struct_0(A_560))
      | ~ v5_waybel_6(B_561,A_560)
      | v1_waybel_7(k5_waybel_0(A_560,B_561),A_560)
      | ~ m1_subset_1(k5_waybel_0(A_560,B_561),k1_zfmisc_1(u1_struct_0(A_560)))
      | ~ v12_waybel_0(k5_waybel_0(A_560,B_561),A_560)
      | ~ v1_waybel_0(k5_waybel_0(A_560,B_561),A_560)
      | v1_xboole_0(k5_waybel_0(A_560,B_561))
      | ~ v2_lattice3(A_560)
      | ~ v5_orders_2(A_560)
      | ~ v4_orders_2(A_560)
      | ~ v3_orders_2(A_560)
      | ~ m1_subset_1(B_561,u1_struct_0(A_560))
      | ~ l1_orders_2(A_560)
      | v2_struct_0(A_560) ) ),
    inference(resolution,[status(thm)],[c_1966,c_16])).

tff(c_1999,plain,(
    ! [A_566,B_567] :
      ( r1_orders_2(A_566,'#skF_2'(A_566,k5_waybel_0(A_566,B_567)),B_567)
      | r1_orders_2(A_566,'#skF_1'(A_566,k5_waybel_0(A_566,B_567)),B_567)
      | ~ m1_subset_1('#skF_1'(A_566,k5_waybel_0(A_566,B_567)),u1_struct_0(A_566))
      | ~ v5_waybel_6(B_567,A_566)
      | ~ m1_subset_1(B_567,u1_struct_0(A_566))
      | v2_struct_0(A_566)
      | v1_waybel_7(k5_waybel_0(A_566,B_567),A_566)
      | ~ m1_subset_1(k5_waybel_0(A_566,B_567),k1_zfmisc_1(u1_struct_0(A_566)))
      | ~ v12_waybel_0(k5_waybel_0(A_566,B_567),A_566)
      | ~ v1_waybel_0(k5_waybel_0(A_566,B_567),A_566)
      | v1_xboole_0(k5_waybel_0(A_566,B_567))
      | ~ l1_orders_2(A_566)
      | ~ v2_lattice3(A_566)
      | ~ v5_orders_2(A_566)
      | ~ v4_orders_2(A_566)
      | ~ v3_orders_2(A_566) ) ),
    inference(resolution,[status(thm)],[c_12,c_1984])).

tff(c_2004,plain,(
    ! [A_568,B_569] :
      ( r1_orders_2(A_568,'#skF_2'(A_568,k5_waybel_0(A_568,B_569)),B_569)
      | r1_orders_2(A_568,'#skF_1'(A_568,k5_waybel_0(A_568,B_569)),B_569)
      | ~ v5_waybel_6(B_569,A_568)
      | ~ m1_subset_1(B_569,u1_struct_0(A_568))
      | v2_struct_0(A_568)
      | v1_waybel_7(k5_waybel_0(A_568,B_569),A_568)
      | ~ m1_subset_1(k5_waybel_0(A_568,B_569),k1_zfmisc_1(u1_struct_0(A_568)))
      | ~ v12_waybel_0(k5_waybel_0(A_568,B_569),A_568)
      | ~ v1_waybel_0(k5_waybel_0(A_568,B_569),A_568)
      | v1_xboole_0(k5_waybel_0(A_568,B_569))
      | ~ l1_orders_2(A_568)
      | ~ v2_lattice3(A_568)
      | ~ v5_orders_2(A_568)
      | ~ v4_orders_2(A_568)
      | ~ v3_orders_2(A_568) ) ),
    inference(resolution,[status(thm)],[c_14,c_1999])).

tff(c_2008,plain,(
    ! [A_570,B_571] :
      ( r1_orders_2(A_570,'#skF_2'(A_570,k5_waybel_0(A_570,B_571)),B_571)
      | r1_orders_2(A_570,'#skF_1'(A_570,k5_waybel_0(A_570,B_571)),B_571)
      | ~ v5_waybel_6(B_571,A_570)
      | v1_waybel_7(k5_waybel_0(A_570,B_571),A_570)
      | ~ v12_waybel_0(k5_waybel_0(A_570,B_571),A_570)
      | ~ v1_waybel_0(k5_waybel_0(A_570,B_571),A_570)
      | v1_xboole_0(k5_waybel_0(A_570,B_571))
      | ~ v2_lattice3(A_570)
      | ~ v5_orders_2(A_570)
      | ~ v4_orders_2(A_570)
      | ~ v3_orders_2(A_570)
      | ~ m1_subset_1(B_571,u1_struct_0(A_570))
      | ~ l1_orders_2(A_570)
      | v2_struct_0(A_570) ) ),
    inference(resolution,[status(thm)],[c_28,c_2004])).

tff(c_38,plain,(
    ! [C_67,A_61,B_65] :
      ( r2_hidden(C_67,k5_waybel_0(A_61,B_65))
      | ~ r1_orders_2(A_61,C_67,B_65)
      | ~ m1_subset_1(C_67,u1_struct_0(A_61))
      | ~ m1_subset_1(B_65,u1_struct_0(A_61))
      | ~ l1_orders_2(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_234,plain,(
    ! [A_119,B_120] :
      ( ~ r2_hidden('#skF_2'(A_119,B_120),B_120)
      | v1_waybel_7(B_120,A_119)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ v12_waybel_0(B_120,A_119)
      | ~ v1_waybel_0(B_120,A_119)
      | v1_xboole_0(B_120)
      | ~ l1_orders_2(A_119)
      | ~ v2_lattice3(A_119)
      | ~ v5_orders_2(A_119)
      | ~ v4_orders_2(A_119)
      | ~ v3_orders_2(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_238,plain,(
    ! [A_61,B_65,A_119] :
      ( v1_waybel_7(k5_waybel_0(A_61,B_65),A_119)
      | ~ m1_subset_1(k5_waybel_0(A_61,B_65),k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ v12_waybel_0(k5_waybel_0(A_61,B_65),A_119)
      | ~ v1_waybel_0(k5_waybel_0(A_61,B_65),A_119)
      | v1_xboole_0(k5_waybel_0(A_61,B_65))
      | ~ l1_orders_2(A_119)
      | ~ v2_lattice3(A_119)
      | ~ v5_orders_2(A_119)
      | ~ v4_orders_2(A_119)
      | ~ v3_orders_2(A_119)
      | ~ r1_orders_2(A_61,'#skF_2'(A_119,k5_waybel_0(A_61,B_65)),B_65)
      | ~ m1_subset_1('#skF_2'(A_119,k5_waybel_0(A_61,B_65)),u1_struct_0(A_61))
      | ~ m1_subset_1(B_65,u1_struct_0(A_61))
      | ~ l1_orders_2(A_61)
      | v2_struct_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_38,c_234])).

tff(c_2036,plain,(
    ! [A_573,B_574] :
      ( ~ m1_subset_1(k5_waybel_0(A_573,B_574),k1_zfmisc_1(u1_struct_0(A_573)))
      | ~ m1_subset_1('#skF_2'(A_573,k5_waybel_0(A_573,B_574)),u1_struct_0(A_573))
      | r1_orders_2(A_573,'#skF_1'(A_573,k5_waybel_0(A_573,B_574)),B_574)
      | ~ v5_waybel_6(B_574,A_573)
      | v1_waybel_7(k5_waybel_0(A_573,B_574),A_573)
      | ~ v12_waybel_0(k5_waybel_0(A_573,B_574),A_573)
      | ~ v1_waybel_0(k5_waybel_0(A_573,B_574),A_573)
      | v1_xboole_0(k5_waybel_0(A_573,B_574))
      | ~ v2_lattice3(A_573)
      | ~ v5_orders_2(A_573)
      | ~ v4_orders_2(A_573)
      | ~ v3_orders_2(A_573)
      | ~ m1_subset_1(B_574,u1_struct_0(A_573))
      | ~ l1_orders_2(A_573)
      | v2_struct_0(A_573) ) ),
    inference(resolution,[status(thm)],[c_2008,c_238])).

tff(c_2041,plain,(
    ! [A_575,B_576] :
      ( r1_orders_2(A_575,'#skF_1'(A_575,k5_waybel_0(A_575,B_576)),B_576)
      | ~ v5_waybel_6(B_576,A_575)
      | ~ m1_subset_1(B_576,u1_struct_0(A_575))
      | v2_struct_0(A_575)
      | v1_waybel_7(k5_waybel_0(A_575,B_576),A_575)
      | ~ m1_subset_1(k5_waybel_0(A_575,B_576),k1_zfmisc_1(u1_struct_0(A_575)))
      | ~ v12_waybel_0(k5_waybel_0(A_575,B_576),A_575)
      | ~ v1_waybel_0(k5_waybel_0(A_575,B_576),A_575)
      | v1_xboole_0(k5_waybel_0(A_575,B_576))
      | ~ l1_orders_2(A_575)
      | ~ v2_lattice3(A_575)
      | ~ v5_orders_2(A_575)
      | ~ v4_orders_2(A_575)
      | ~ v3_orders_2(A_575) ) ),
    inference(resolution,[status(thm)],[c_12,c_2036])).

tff(c_2045,plain,(
    ! [A_577,B_578] :
      ( r1_orders_2(A_577,'#skF_1'(A_577,k5_waybel_0(A_577,B_578)),B_578)
      | ~ v5_waybel_6(B_578,A_577)
      | v1_waybel_7(k5_waybel_0(A_577,B_578),A_577)
      | ~ v12_waybel_0(k5_waybel_0(A_577,B_578),A_577)
      | ~ v1_waybel_0(k5_waybel_0(A_577,B_578),A_577)
      | v1_xboole_0(k5_waybel_0(A_577,B_578))
      | ~ v2_lattice3(A_577)
      | ~ v5_orders_2(A_577)
      | ~ v4_orders_2(A_577)
      | ~ v3_orders_2(A_577)
      | ~ m1_subset_1(B_578,u1_struct_0(A_577))
      | ~ l1_orders_2(A_577)
      | v2_struct_0(A_577) ) ),
    inference(resolution,[status(thm)],[c_28,c_2041])).

tff(c_193,plain,(
    ! [A_113,B_114] :
      ( ~ r2_hidden('#skF_1'(A_113,B_114),B_114)
      | v1_waybel_7(B_114,A_113)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ v12_waybel_0(B_114,A_113)
      | ~ v1_waybel_0(B_114,A_113)
      | v1_xboole_0(B_114)
      | ~ l1_orders_2(A_113)
      | ~ v2_lattice3(A_113)
      | ~ v5_orders_2(A_113)
      | ~ v4_orders_2(A_113)
      | ~ v3_orders_2(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_197,plain,(
    ! [A_61,B_65,A_113] :
      ( v1_waybel_7(k5_waybel_0(A_61,B_65),A_113)
      | ~ m1_subset_1(k5_waybel_0(A_61,B_65),k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ v12_waybel_0(k5_waybel_0(A_61,B_65),A_113)
      | ~ v1_waybel_0(k5_waybel_0(A_61,B_65),A_113)
      | v1_xboole_0(k5_waybel_0(A_61,B_65))
      | ~ l1_orders_2(A_113)
      | ~ v2_lattice3(A_113)
      | ~ v5_orders_2(A_113)
      | ~ v4_orders_2(A_113)
      | ~ v3_orders_2(A_113)
      | ~ r1_orders_2(A_61,'#skF_1'(A_113,k5_waybel_0(A_61,B_65)),B_65)
      | ~ m1_subset_1('#skF_1'(A_113,k5_waybel_0(A_61,B_65)),u1_struct_0(A_61))
      | ~ m1_subset_1(B_65,u1_struct_0(A_61))
      | ~ l1_orders_2(A_61)
      | v2_struct_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_38,c_193])).

tff(c_2049,plain,(
    ! [A_579,B_580] :
      ( ~ m1_subset_1(k5_waybel_0(A_579,B_580),k1_zfmisc_1(u1_struct_0(A_579)))
      | ~ m1_subset_1('#skF_1'(A_579,k5_waybel_0(A_579,B_580)),u1_struct_0(A_579))
      | ~ v5_waybel_6(B_580,A_579)
      | v1_waybel_7(k5_waybel_0(A_579,B_580),A_579)
      | ~ v12_waybel_0(k5_waybel_0(A_579,B_580),A_579)
      | ~ v1_waybel_0(k5_waybel_0(A_579,B_580),A_579)
      | v1_xboole_0(k5_waybel_0(A_579,B_580))
      | ~ v2_lattice3(A_579)
      | ~ v5_orders_2(A_579)
      | ~ v4_orders_2(A_579)
      | ~ v3_orders_2(A_579)
      | ~ m1_subset_1(B_580,u1_struct_0(A_579))
      | ~ l1_orders_2(A_579)
      | v2_struct_0(A_579) ) ),
    inference(resolution,[status(thm)],[c_2045,c_197])).

tff(c_2055,plain,(
    ! [B_581,A_582] :
      ( ~ v5_waybel_6(B_581,A_582)
      | ~ m1_subset_1(B_581,u1_struct_0(A_582))
      | v2_struct_0(A_582)
      | v1_waybel_7(k5_waybel_0(A_582,B_581),A_582)
      | ~ m1_subset_1(k5_waybel_0(A_582,B_581),k1_zfmisc_1(u1_struct_0(A_582)))
      | ~ v12_waybel_0(k5_waybel_0(A_582,B_581),A_582)
      | ~ v1_waybel_0(k5_waybel_0(A_582,B_581),A_582)
      | v1_xboole_0(k5_waybel_0(A_582,B_581))
      | ~ l1_orders_2(A_582)
      | ~ v2_lattice3(A_582)
      | ~ v5_orders_2(A_582)
      | ~ v4_orders_2(A_582)
      | ~ v3_orders_2(A_582) ) ),
    inference(resolution,[status(thm)],[c_14,c_2049])).

tff(c_2066,plain,(
    ! [B_587,A_588] :
      ( ~ v5_waybel_6(B_587,A_588)
      | v1_waybel_7(k5_waybel_0(A_588,B_587),A_588)
      | ~ v12_waybel_0(k5_waybel_0(A_588,B_587),A_588)
      | ~ v1_waybel_0(k5_waybel_0(A_588,B_587),A_588)
      | v1_xboole_0(k5_waybel_0(A_588,B_587))
      | ~ v2_lattice3(A_588)
      | ~ v5_orders_2(A_588)
      | ~ v4_orders_2(A_588)
      | ~ v3_orders_2(A_588)
      | ~ m1_subset_1(B_587,u1_struct_0(A_588))
      | ~ l1_orders_2(A_588)
      | v2_struct_0(A_588) ) ),
    inference(resolution,[status(thm)],[c_28,c_2055])).

tff(c_44,plain,(
    ~ v1_waybel_7(k5_waybel_0('#skF_5','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_2069,plain,
    ( ~ v5_waybel_6('#skF_6','#skF_5')
    | ~ v12_waybel_0(k5_waybel_0('#skF_5','#skF_6'),'#skF_5')
    | ~ v1_waybel_0(k5_waybel_0('#skF_5','#skF_6'),'#skF_5')
    | v1_xboole_0(k5_waybel_0('#skF_5','#skF_6'))
    | ~ v2_lattice3('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2066,c_44])).

tff(c_2072,plain,
    ( ~ v12_waybel_0(k5_waybel_0('#skF_5','#skF_6'),'#skF_5')
    | ~ v1_waybel_0(k5_waybel_0('#skF_5','#skF_6'),'#skF_5')
    | v1_xboole_0(k5_waybel_0('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_60,c_58,c_56,c_52,c_46,c_2069])).

tff(c_2073,plain,
    ( ~ v12_waybel_0(k5_waybel_0('#skF_5','#skF_6'),'#skF_5')
    | ~ v1_waybel_0(k5_waybel_0('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_70,c_2072])).

tff(c_2074,plain,(
    ~ v1_waybel_0(k5_waybel_0('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2073])).

tff(c_2077,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_2074])).

tff(c_2080,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_48,c_2077])).

tff(c_2082,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_2080])).

tff(c_2083,plain,(
    ~ v12_waybel_0(k5_waybel_0('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_2073])).

tff(c_2087,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_2083])).

tff(c_2090,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_50,c_48,c_2087])).

tff(c_2092,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_2090])).

tff(c_2093,plain,(
    v2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_2097,plain,
    ( ~ v2_lattice3('#skF_5')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_2093,c_2])).

tff(c_2101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_2097])).

%------------------------------------------------------------------------------
