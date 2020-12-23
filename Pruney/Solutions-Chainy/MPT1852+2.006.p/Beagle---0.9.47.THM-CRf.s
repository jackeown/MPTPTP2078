%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:59 EST 2020

% Result     : Theorem 4.82s
% Output     : CNFRefutation 4.82s
% Verified   : 
% Statistics : Number of formulae       :  131 (1239 expanded)
%              Number of leaves         :   29 ( 427 expanded)
%              Depth                    :   25
%              Number of atoms          :  313 (3611 expanded)
%              Number of equality atoms :   12 ( 431 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > l1_pre_topc > k6_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( l1_pre_topc(B)
           => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                & v3_tdlat_3(A) )
             => v3_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tex_2)).

tff(f_116,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( r2_hidden(B,u1_pre_topc(A))
             => r2_hidden(k6_subset_1(u1_struct_0(A),B),u1_pre_topc(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tdlat_3)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
             => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_2)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v1_tops_2(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C))))
                   => ( D = B
                     => v1_tops_2(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_2)).

tff(c_38,plain,(
    ~ v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_34,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_1'(A_42),u1_pre_topc(A_42))
      | v3_tdlat_3(A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_36,plain,(
    ! [A_42] :
      ( m1_subset_1('#skF_1'(A_42),k1_zfmisc_1(u1_struct_0(A_42)))
      | v3_tdlat_3(A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_40,plain,(
    v3_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_26,plain,(
    ! [A_38] :
      ( m1_pre_topc(A_38,A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_16,plain,(
    ! [A_10,B_12] :
      ( m1_pre_topc(A_10,g1_pre_topc(u1_struct_0(B_12),u1_pre_topc(B_12)))
      | ~ m1_pre_topc(A_10,B_12)
      | ~ l1_pre_topc(B_12)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_42,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_74,plain,(
    ! [B_59,A_60] :
      ( m1_pre_topc(B_59,A_60)
      | ~ m1_pre_topc(B_59,g1_pre_topc(u1_struct_0(A_60),u1_pre_topc(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_77,plain,(
    ! [B_59] :
      ( m1_pre_topc(B_59,'#skF_2')
      | ~ m1_pre_topc(B_59,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_74])).

tff(c_99,plain,(
    ! [B_63] :
      ( m1_pre_topc(B_63,'#skF_2')
      | ~ m1_pre_topc(B_63,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_77])).

tff(c_103,plain,(
    ! [A_10] :
      ( m1_pre_topc(A_10,'#skF_2')
      | ~ m1_pre_topc(A_10,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_10) ) ),
    inference(resolution,[status(thm)],[c_16,c_99])).

tff(c_110,plain,(
    ! [A_10] :
      ( m1_pre_topc(A_10,'#skF_2')
      | ~ m1_pre_topc(A_10,'#skF_3')
      | ~ l1_pre_topc(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_103])).

tff(c_85,plain,(
    ! [A_61,B_62] :
      ( m1_pre_topc(A_61,g1_pre_topc(u1_struct_0(B_62),u1_pre_topc(B_62)))
      | ~ m1_pre_topc(A_61,B_62)
      | ~ l1_pre_topc(B_62)
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_94,plain,(
    ! [A_61] :
      ( m1_pre_topc(A_61,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_61,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_85])).

tff(c_119,plain,(
    ! [A_65] :
      ( m1_pre_topc(A_65,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_65,'#skF_2')
      | ~ l1_pre_topc(A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_94])).

tff(c_12,plain,(
    ! [B_9,A_7] :
      ( m1_pre_topc(B_9,A_7)
      | ~ m1_pre_topc(B_9,g1_pre_topc(u1_struct_0(A_7),u1_pre_topc(A_7)))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_125,plain,(
    ! [A_65] :
      ( m1_pre_topc(A_65,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(A_65,'#skF_2')
      | ~ l1_pre_topc(A_65) ) ),
    inference(resolution,[status(thm)],[c_119,c_12])).

tff(c_135,plain,(
    ! [A_66] :
      ( m1_pre_topc(A_66,'#skF_3')
      | ~ m1_pre_topc(A_66,'#skF_2')
      | ~ l1_pre_topc(A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_125])).

tff(c_142,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_135])).

tff(c_146,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_142])).

tff(c_28,plain,(
    ! [B_41,A_39] :
      ( r1_tarski(u1_struct_0(B_41),u1_struct_0(A_39))
      | ~ m1_pre_topc(B_41,A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_68,plain,(
    ! [B_55,A_56] :
      ( r1_tarski(u1_struct_0(B_55),u1_struct_0(A_56))
      | ~ m1_pre_topc(B_55,A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_153,plain,(
    ! [B_67,A_68] :
      ( u1_struct_0(B_67) = u1_struct_0(A_68)
      | ~ r1_tarski(u1_struct_0(A_68),u1_struct_0(B_67))
      | ~ m1_pre_topc(B_67,A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_68,c_2])).

tff(c_164,plain,(
    ! [B_69,A_70] :
      ( u1_struct_0(B_69) = u1_struct_0(A_70)
      | ~ m1_pre_topc(A_70,B_69)
      | ~ l1_pre_topc(B_69)
      | ~ m1_pre_topc(B_69,A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_28,c_153])).

tff(c_166,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_146,c_164])).

tff(c_177,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_166])).

tff(c_193,plain,(
    ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_196,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_110,c_193])).

tff(c_199,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_196])).

tff(c_202,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_199])).

tff(c_206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_202])).

tff(c_207,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_208,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_6] :
      ( m1_subset_1(u1_pre_topc(A_6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_6))))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1543,plain,(
    ! [C_128,A_129,B_130] :
      ( m1_subset_1(C_128,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_129))))
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_130))))
      | ~ m1_pre_topc(B_130,A_129)
      | ~ l1_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1792,plain,(
    ! [A_146,A_147] :
      ( m1_subset_1(u1_pre_topc(A_146),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_147))))
      | ~ m1_pre_topc(A_146,A_147)
      | ~ l1_pre_topc(A_147)
      | ~ l1_pre_topc(A_146) ) ),
    inference(resolution,[status(thm)],[c_10,c_1543])).

tff(c_1813,plain,(
    ! [A_146] :
      ( m1_subset_1(u1_pre_topc(A_146),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | ~ m1_pre_topc(A_146,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_1792])).

tff(c_1826,plain,(
    ! [A_148] :
      ( m1_subset_1(u1_pre_topc(A_148),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | ~ m1_pre_topc(A_148,'#skF_2')
      | ~ l1_pre_topc(A_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1813])).

tff(c_22,plain,(
    ! [B_37,A_35] :
      ( v1_tops_2(B_37,A_35)
      | ~ r1_tarski(B_37,u1_pre_topc(A_35))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_35))))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1842,plain,(
    ! [A_148] :
      ( v1_tops_2(u1_pre_topc(A_148),'#skF_3')
      | ~ r1_tarski(u1_pre_topc(A_148),u1_pre_topc('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(A_148,'#skF_2')
      | ~ l1_pre_topc(A_148) ) ),
    inference(resolution,[status(thm)],[c_1826,c_22])).

tff(c_1902,plain,(
    ! [A_152] :
      ( v1_tops_2(u1_pre_topc(A_152),'#skF_3')
      | ~ r1_tarski(u1_pre_topc(A_152),u1_pre_topc('#skF_3'))
      | ~ m1_pre_topc(A_152,'#skF_2')
      | ~ l1_pre_topc(A_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1842])).

tff(c_1909,plain,
    ( v1_tops_2(u1_pre_topc('#skF_3'),'#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_1902])).

tff(c_1915,plain,(
    v1_tops_2(u1_pre_topc('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_208,c_1909])).

tff(c_2022,plain,(
    ! [C_158,A_159] :
      ( m1_subset_1(C_158,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_159))))
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | ~ m1_pre_topc('#skF_2',A_159)
      | ~ l1_pre_topc(A_159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_1543])).

tff(c_2035,plain,(
    ! [A_159] :
      ( m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_159))))
      | ~ m1_pre_topc('#skF_2',A_159)
      | ~ l1_pre_topc(A_159)
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10,c_2022])).

tff(c_2087,plain,(
    ! [A_161] :
      ( m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_161))))
      | ~ m1_pre_topc('#skF_2',A_161)
      | ~ l1_pre_topc(A_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2035])).

tff(c_2111,plain,
    ( m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_2087])).

tff(c_2128,plain,
    ( m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2111])).

tff(c_2129,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2128])).

tff(c_2132,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_110,c_2129])).

tff(c_2139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_146,c_2132])).

tff(c_2140,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_2128])).

tff(c_269,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_10])).

tff(c_288,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_269])).

tff(c_242,plain,(
    ! [B_37] :
      ( v1_tops_2(B_37,'#skF_2')
      | ~ r1_tarski(B_37,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_22])).

tff(c_524,plain,(
    ! [B_90] :
      ( v1_tops_2(B_90,'#skF_2')
      | ~ r1_tarski(B_90,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_242])).

tff(c_531,plain,
    ( v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2')
    | ~ r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_288,c_524])).

tff(c_541,plain,(
    v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_531])).

tff(c_297,plain,(
    ! [B_74,A_75] :
      ( r1_tarski(B_74,u1_pre_topc(A_75))
      | ~ v1_tops_2(B_74,A_75)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_75))))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_300,plain,
    ( r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_3'))
    | ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_288,c_297])).

tff(c_309,plain,
    ( r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_3'))
    | ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_300])).

tff(c_326,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_309])).

tff(c_606,plain,(
    ! [D_95,C_96,A_97] :
      ( v1_tops_2(D_95,C_96)
      | ~ m1_subset_1(D_95,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_96))))
      | ~ v1_tops_2(D_95,A_97)
      | ~ m1_pre_topc(C_96,A_97)
      | ~ m1_subset_1(D_95,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_97))))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_612,plain,(
    ! [A_97] :
      ( v1_tops_2(u1_pre_topc('#skF_2'),'#skF_3')
      | ~ v1_tops_2(u1_pre_topc('#skF_2'),A_97)
      | ~ m1_pre_topc('#skF_3',A_97)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_97))))
      | ~ l1_pre_topc(A_97) ) ),
    inference(resolution,[status(thm)],[c_288,c_606])).

tff(c_1492,plain,(
    ! [A_127] :
      ( ~ v1_tops_2(u1_pre_topc('#skF_2'),A_127)
      | ~ m1_pre_topc('#skF_3',A_127)
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_127))))
      | ~ l1_pre_topc(A_127) ) ),
    inference(negUnitSimplification,[status(thm)],[c_326,c_612])).

tff(c_1512,plain,
    ( ~ v1_tops_2(u1_pre_topc('#skF_2'),'#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_1492])).

tff(c_1530,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_288,c_208,c_541,c_1512])).

tff(c_1531,plain,(
    r1_tarski(u1_pre_topc('#skF_2'),u1_pre_topc('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_309])).

tff(c_1539,plain,
    ( u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3')
    | ~ r1_tarski(u1_pre_topc('#skF_3'),u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1531,c_2])).

tff(c_1542,plain,(
    ~ r1_tarski(u1_pre_topc('#skF_3'),u1_pre_topc('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1539])).

tff(c_303,plain,(
    ! [B_74] :
      ( r1_tarski(B_74,u1_pre_topc('#skF_2'))
      | ~ v1_tops_2(B_74,'#skF_2')
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_297])).

tff(c_1735,plain,(
    ! [B_141] :
      ( r1_tarski(B_141,u1_pre_topc('#skF_2'))
      | ~ v1_tops_2(B_141,'#skF_2')
      | ~ m1_subset_1(B_141,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_303])).

tff(c_1746,plain,
    ( r1_tarski(u1_pre_topc('#skF_3'),u1_pre_topc('#skF_2'))
    | ~ v1_tops_2(u1_pre_topc('#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_1735])).

tff(c_1754,plain,
    ( r1_tarski(u1_pre_topc('#skF_3'),u1_pre_topc('#skF_2'))
    | ~ v1_tops_2(u1_pre_topc('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1746])).

tff(c_1755,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1542,c_1754])).

tff(c_1779,plain,(
    ! [D_143,C_144,A_145] :
      ( v1_tops_2(D_143,C_144)
      | ~ m1_subset_1(D_143,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_144))))
      | ~ v1_tops_2(D_143,A_145)
      | ~ m1_pre_topc(C_144,A_145)
      | ~ m1_subset_1(D_143,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_145))))
      | ~ l1_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2279,plain,(
    ! [D_165,A_166] :
      ( v1_tops_2(D_165,'#skF_2')
      | ~ m1_subset_1(D_165,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | ~ v1_tops_2(D_165,A_166)
      | ~ m1_pre_topc('#skF_2',A_166)
      | ~ m1_subset_1(D_165,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_166))))
      | ~ l1_pre_topc(A_166) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_1779])).

tff(c_2303,plain,(
    ! [A_166] :
      ( v1_tops_2(u1_pre_topc('#skF_3'),'#skF_2')
      | ~ v1_tops_2(u1_pre_topc('#skF_3'),A_166)
      | ~ m1_pre_topc('#skF_2',A_166)
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_166))))
      | ~ l1_pre_topc(A_166)
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10,c_2279])).

tff(c_2329,plain,(
    ! [A_166] :
      ( v1_tops_2(u1_pre_topc('#skF_3'),'#skF_2')
      | ~ v1_tops_2(u1_pre_topc('#skF_3'),A_166)
      | ~ m1_pre_topc('#skF_2',A_166)
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_166))))
      | ~ l1_pre_topc(A_166) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2303])).

tff(c_2698,plain,(
    ! [A_178] :
      ( ~ v1_tops_2(u1_pre_topc('#skF_3'),A_178)
      | ~ m1_pre_topc('#skF_2',A_178)
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_178))))
      | ~ l1_pre_topc(A_178) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1755,c_2329])).

tff(c_2704,plain,
    ( ~ v1_tops_2(u1_pre_topc('#skF_3'),'#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2140,c_2698])).

tff(c_2727,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_146,c_1915,c_2704])).

tff(c_2728,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1539])).

tff(c_2904,plain,(
    ! [A_187,B_188] :
      ( r2_hidden(k6_subset_1(u1_struct_0(A_187),B_188),u1_pre_topc(A_187))
      | ~ r2_hidden(B_188,u1_pre_topc(A_187))
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0(A_187)))
      | ~ v3_tdlat_3(A_187)
      | ~ l1_pre_topc(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2914,plain,(
    ! [B_188] :
      ( r2_hidden(k6_subset_1(u1_struct_0('#skF_3'),B_188),u1_pre_topc('#skF_2'))
      | ~ r2_hidden(B_188,u1_pre_topc('#skF_2'))
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ v3_tdlat_3('#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_2904])).

tff(c_3663,plain,(
    ! [B_222] :
      ( r2_hidden(k6_subset_1(u1_struct_0('#skF_3'),B_222),u1_pre_topc('#skF_3'))
      | ~ r2_hidden(B_222,u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(B_222,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_207,c_2728,c_2728,c_2914])).

tff(c_32,plain,(
    ! [A_42] :
      ( ~ r2_hidden(k6_subset_1(u1_struct_0(A_42),'#skF_1'(A_42)),u1_pre_topc(A_42))
      | v3_tdlat_3(A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3667,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_3663,c_32])).

tff(c_3670,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3667])).

tff(c_3671,plain,
    ( ~ r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_3670])).

tff(c_3672,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_3671])).

tff(c_3675,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_3672])).

tff(c_3678,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3675])).

tff(c_3680,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_3678])).

tff(c_3681,plain,(
    ~ r2_hidden('#skF_1'('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3671])).

tff(c_3685,plain,
    ( v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_3681])).

tff(c_3688,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3685])).

tff(c_3690,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_3688])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:10:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.82/1.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.87  
% 4.82/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.87  %$ v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v3_tdlat_3 > l1_pre_topc > k6_subset_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 4.82/1.87  
% 4.82/1.87  %Foreground sorts:
% 4.82/1.87  
% 4.82/1.87  
% 4.82/1.87  %Background operators:
% 4.82/1.87  
% 4.82/1.87  
% 4.82/1.87  %Foreground operators:
% 4.82/1.87  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.82/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.82/1.87  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.82/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.82/1.87  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.82/1.87  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 4.82/1.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.82/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.82/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.82/1.87  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 4.82/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.82/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.82/1.87  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 4.82/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.82/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.82/1.87  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.82/1.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.82/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.82/1.87  
% 4.82/1.89  tff(f_128, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & v3_tdlat_3(A)) => v3_tdlat_3(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_tex_2)).
% 4.82/1.89  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) => r2_hidden(k6_subset_1(u1_struct_0(A), B), u1_pre_topc(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tdlat_3)).
% 4.82/1.89  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.82/1.89  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 4.82/1.89  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 4.82/1.89  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 4.82/1.89  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.82/1.89  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 4.82/1.89  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tops_2)).
% 4.82/1.89  tff(f_94, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tops_2)).
% 4.82/1.89  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_pre_topc(C, A) => (v1_tops_2(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C)))) => ((D = B) => v1_tops_2(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tops_2)).
% 4.82/1.89  tff(c_38, plain, (~v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.82/1.89  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.82/1.89  tff(c_34, plain, (![A_42]: (r2_hidden('#skF_1'(A_42), u1_pre_topc(A_42)) | v3_tdlat_3(A_42) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.82/1.89  tff(c_36, plain, (![A_42]: (m1_subset_1('#skF_1'(A_42), k1_zfmisc_1(u1_struct_0(A_42))) | v3_tdlat_3(A_42) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.82/1.89  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.82/1.89  tff(c_40, plain, (v3_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.82/1.89  tff(c_26, plain, (![A_38]: (m1_pre_topc(A_38, A_38) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.82/1.89  tff(c_16, plain, (![A_10, B_12]: (m1_pre_topc(A_10, g1_pre_topc(u1_struct_0(B_12), u1_pre_topc(B_12))) | ~m1_pre_topc(A_10, B_12) | ~l1_pre_topc(B_12) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.82/1.89  tff(c_42, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.82/1.89  tff(c_74, plain, (![B_59, A_60]: (m1_pre_topc(B_59, A_60) | ~m1_pre_topc(B_59, g1_pre_topc(u1_struct_0(A_60), u1_pre_topc(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.82/1.89  tff(c_77, plain, (![B_59]: (m1_pre_topc(B_59, '#skF_2') | ~m1_pre_topc(B_59, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_74])).
% 4.82/1.89  tff(c_99, plain, (![B_63]: (m1_pre_topc(B_63, '#skF_2') | ~m1_pre_topc(B_63, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_77])).
% 4.82/1.89  tff(c_103, plain, (![A_10]: (m1_pre_topc(A_10, '#skF_2') | ~m1_pre_topc(A_10, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_10))), inference(resolution, [status(thm)], [c_16, c_99])).
% 4.82/1.89  tff(c_110, plain, (![A_10]: (m1_pre_topc(A_10, '#skF_2') | ~m1_pre_topc(A_10, '#skF_3') | ~l1_pre_topc(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_103])).
% 4.82/1.89  tff(c_85, plain, (![A_61, B_62]: (m1_pre_topc(A_61, g1_pre_topc(u1_struct_0(B_62), u1_pre_topc(B_62))) | ~m1_pre_topc(A_61, B_62) | ~l1_pre_topc(B_62) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.82/1.89  tff(c_94, plain, (![A_61]: (m1_pre_topc(A_61, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_61, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_61))), inference(superposition, [status(thm), theory('equality')], [c_42, c_85])).
% 4.82/1.89  tff(c_119, plain, (![A_65]: (m1_pre_topc(A_65, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_65, '#skF_2') | ~l1_pre_topc(A_65))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_94])).
% 4.82/1.89  tff(c_12, plain, (![B_9, A_7]: (m1_pre_topc(B_9, A_7) | ~m1_pre_topc(B_9, g1_pre_topc(u1_struct_0(A_7), u1_pre_topc(A_7))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.82/1.89  tff(c_125, plain, (![A_65]: (m1_pre_topc(A_65, '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(A_65, '#skF_2') | ~l1_pre_topc(A_65))), inference(resolution, [status(thm)], [c_119, c_12])).
% 4.82/1.89  tff(c_135, plain, (![A_66]: (m1_pre_topc(A_66, '#skF_3') | ~m1_pre_topc(A_66, '#skF_2') | ~l1_pre_topc(A_66))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_125])).
% 4.82/1.89  tff(c_142, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_135])).
% 4.82/1.89  tff(c_146, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_142])).
% 4.82/1.89  tff(c_28, plain, (![B_41, A_39]: (r1_tarski(u1_struct_0(B_41), u1_struct_0(A_39)) | ~m1_pre_topc(B_41, A_39) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.82/1.89  tff(c_68, plain, (![B_55, A_56]: (r1_tarski(u1_struct_0(B_55), u1_struct_0(A_56)) | ~m1_pre_topc(B_55, A_56) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.82/1.89  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.82/1.89  tff(c_153, plain, (![B_67, A_68]: (u1_struct_0(B_67)=u1_struct_0(A_68) | ~r1_tarski(u1_struct_0(A_68), u1_struct_0(B_67)) | ~m1_pre_topc(B_67, A_68) | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_68, c_2])).
% 4.82/1.89  tff(c_164, plain, (![B_69, A_70]: (u1_struct_0(B_69)=u1_struct_0(A_70) | ~m1_pre_topc(A_70, B_69) | ~l1_pre_topc(B_69) | ~m1_pre_topc(B_69, A_70) | ~l1_pre_topc(A_70))), inference(resolution, [status(thm)], [c_28, c_153])).
% 4.82/1.89  tff(c_166, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_146, c_164])).
% 4.82/1.89  tff(c_177, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_166])).
% 4.82/1.89  tff(c_193, plain, (~m1_pre_topc('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_177])).
% 4.82/1.89  tff(c_196, plain, (~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_110, c_193])).
% 4.82/1.89  tff(c_199, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_196])).
% 4.82/1.89  tff(c_202, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_26, c_199])).
% 4.82/1.89  tff(c_206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_202])).
% 4.82/1.89  tff(c_207, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_177])).
% 4.82/1.89  tff(c_208, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_177])).
% 4.82/1.89  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.82/1.89  tff(c_10, plain, (![A_6]: (m1_subset_1(u1_pre_topc(A_6), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_6)))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.82/1.89  tff(c_1543, plain, (![C_128, A_129, B_130]: (m1_subset_1(C_128, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_129)))) | ~m1_subset_1(C_128, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B_130)))) | ~m1_pre_topc(B_130, A_129) | ~l1_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.82/1.89  tff(c_1792, plain, (![A_146, A_147]: (m1_subset_1(u1_pre_topc(A_146), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_147)))) | ~m1_pre_topc(A_146, A_147) | ~l1_pre_topc(A_147) | ~l1_pre_topc(A_146))), inference(resolution, [status(thm)], [c_10, c_1543])).
% 4.82/1.89  tff(c_1813, plain, (![A_146]: (m1_subset_1(u1_pre_topc(A_146), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~m1_pre_topc(A_146, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_146))), inference(superposition, [status(thm), theory('equality')], [c_207, c_1792])).
% 4.82/1.89  tff(c_1826, plain, (![A_148]: (m1_subset_1(u1_pre_topc(A_148), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~m1_pre_topc(A_148, '#skF_2') | ~l1_pre_topc(A_148))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1813])).
% 4.82/1.89  tff(c_22, plain, (![B_37, A_35]: (v1_tops_2(B_37, A_35) | ~r1_tarski(B_37, u1_pre_topc(A_35)) | ~m1_subset_1(B_37, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_35)))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.82/1.89  tff(c_1842, plain, (![A_148]: (v1_tops_2(u1_pre_topc(A_148), '#skF_3') | ~r1_tarski(u1_pre_topc(A_148), u1_pre_topc('#skF_3')) | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(A_148, '#skF_2') | ~l1_pre_topc(A_148))), inference(resolution, [status(thm)], [c_1826, c_22])).
% 4.82/1.89  tff(c_1902, plain, (![A_152]: (v1_tops_2(u1_pre_topc(A_152), '#skF_3') | ~r1_tarski(u1_pre_topc(A_152), u1_pre_topc('#skF_3')) | ~m1_pre_topc(A_152, '#skF_2') | ~l1_pre_topc(A_152))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1842])).
% 4.82/1.89  tff(c_1909, plain, (v1_tops_2(u1_pre_topc('#skF_3'), '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_1902])).
% 4.82/1.89  tff(c_1915, plain, (v1_tops_2(u1_pre_topc('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_208, c_1909])).
% 4.82/1.89  tff(c_2022, plain, (![C_158, A_159]: (m1_subset_1(C_158, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_159)))) | ~m1_subset_1(C_158, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~m1_pre_topc('#skF_2', A_159) | ~l1_pre_topc(A_159))), inference(superposition, [status(thm), theory('equality')], [c_207, c_1543])).
% 4.82/1.89  tff(c_2035, plain, (![A_159]: (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_159)))) | ~m1_pre_topc('#skF_2', A_159) | ~l1_pre_topc(A_159) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_10, c_2022])).
% 4.82/1.89  tff(c_2087, plain, (![A_161]: (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_161)))) | ~m1_pre_topc('#skF_2', A_161) | ~l1_pre_topc(A_161))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2035])).
% 4.82/1.89  tff(c_2111, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_207, c_2087])).
% 4.82/1.89  tff(c_2128, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2111])).
% 4.82/1.89  tff(c_2129, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_2128])).
% 4.82/1.89  tff(c_2132, plain, (~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_110, c_2129])).
% 4.82/1.89  tff(c_2139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_146, c_2132])).
% 4.82/1.89  tff(c_2140, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitRight, [status(thm)], [c_2128])).
% 4.82/1.89  tff(c_269, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_207, c_10])).
% 4.82/1.89  tff(c_288, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_269])).
% 4.82/1.89  tff(c_242, plain, (![B_37]: (v1_tops_2(B_37, '#skF_2') | ~r1_tarski(B_37, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_37, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_207, c_22])).
% 4.82/1.89  tff(c_524, plain, (![B_90]: (v1_tops_2(B_90, '#skF_2') | ~r1_tarski(B_90, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_90, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_242])).
% 4.82/1.89  tff(c_531, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2') | ~r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_288, c_524])).
% 4.82/1.89  tff(c_541, plain, (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_531])).
% 4.82/1.89  tff(c_297, plain, (![B_74, A_75]: (r1_tarski(B_74, u1_pre_topc(A_75)) | ~v1_tops_2(B_74, A_75) | ~m1_subset_1(B_74, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_75)))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.82/1.89  tff(c_300, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_3')) | ~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_288, c_297])).
% 4.82/1.89  tff(c_309, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_3')) | ~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_300])).
% 4.82/1.89  tff(c_326, plain, (~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_309])).
% 4.82/1.89  tff(c_606, plain, (![D_95, C_96, A_97]: (v1_tops_2(D_95, C_96) | ~m1_subset_1(D_95, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_96)))) | ~v1_tops_2(D_95, A_97) | ~m1_pre_topc(C_96, A_97) | ~m1_subset_1(D_95, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_97)))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.82/1.89  tff(c_612, plain, (![A_97]: (v1_tops_2(u1_pre_topc('#skF_2'), '#skF_3') | ~v1_tops_2(u1_pre_topc('#skF_2'), A_97) | ~m1_pre_topc('#skF_3', A_97) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_97)))) | ~l1_pre_topc(A_97))), inference(resolution, [status(thm)], [c_288, c_606])).
% 4.82/1.89  tff(c_1492, plain, (![A_127]: (~v1_tops_2(u1_pre_topc('#skF_2'), A_127) | ~m1_pre_topc('#skF_3', A_127) | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_127)))) | ~l1_pre_topc(A_127))), inference(negUnitSimplification, [status(thm)], [c_326, c_612])).
% 4.82/1.89  tff(c_1512, plain, (~v1_tops_2(u1_pre_topc('#skF_2'), '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_207, c_1492])).
% 4.82/1.89  tff(c_1530, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_288, c_208, c_541, c_1512])).
% 4.82/1.89  tff(c_1531, plain, (r1_tarski(u1_pre_topc('#skF_2'), u1_pre_topc('#skF_3'))), inference(splitRight, [status(thm)], [c_309])).
% 4.82/1.89  tff(c_1539, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3') | ~r1_tarski(u1_pre_topc('#skF_3'), u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_1531, c_2])).
% 4.82/1.89  tff(c_1542, plain, (~r1_tarski(u1_pre_topc('#skF_3'), u1_pre_topc('#skF_2'))), inference(splitLeft, [status(thm)], [c_1539])).
% 4.82/1.89  tff(c_303, plain, (![B_74]: (r1_tarski(B_74, u1_pre_topc('#skF_2')) | ~v1_tops_2(B_74, '#skF_2') | ~m1_subset_1(B_74, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_207, c_297])).
% 4.82/1.89  tff(c_1735, plain, (![B_141]: (r1_tarski(B_141, u1_pre_topc('#skF_2')) | ~v1_tops_2(B_141, '#skF_2') | ~m1_subset_1(B_141, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_303])).
% 4.82/1.89  tff(c_1746, plain, (r1_tarski(u1_pre_topc('#skF_3'), u1_pre_topc('#skF_2')) | ~v1_tops_2(u1_pre_topc('#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_10, c_1735])).
% 4.82/1.89  tff(c_1754, plain, (r1_tarski(u1_pre_topc('#skF_3'), u1_pre_topc('#skF_2')) | ~v1_tops_2(u1_pre_topc('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1746])).
% 4.82/1.89  tff(c_1755, plain, (~v1_tops_2(u1_pre_topc('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_1542, c_1754])).
% 4.82/1.89  tff(c_1779, plain, (![D_143, C_144, A_145]: (v1_tops_2(D_143, C_144) | ~m1_subset_1(D_143, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C_144)))) | ~v1_tops_2(D_143, A_145) | ~m1_pre_topc(C_144, A_145) | ~m1_subset_1(D_143, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_145)))) | ~l1_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.82/1.89  tff(c_2279, plain, (![D_165, A_166]: (v1_tops_2(D_165, '#skF_2') | ~m1_subset_1(D_165, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~v1_tops_2(D_165, A_166) | ~m1_pre_topc('#skF_2', A_166) | ~m1_subset_1(D_165, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_166)))) | ~l1_pre_topc(A_166))), inference(superposition, [status(thm), theory('equality')], [c_207, c_1779])).
% 4.82/1.89  tff(c_2303, plain, (![A_166]: (v1_tops_2(u1_pre_topc('#skF_3'), '#skF_2') | ~v1_tops_2(u1_pre_topc('#skF_3'), A_166) | ~m1_pre_topc('#skF_2', A_166) | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_166)))) | ~l1_pre_topc(A_166) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_10, c_2279])).
% 4.82/1.89  tff(c_2329, plain, (![A_166]: (v1_tops_2(u1_pre_topc('#skF_3'), '#skF_2') | ~v1_tops_2(u1_pre_topc('#skF_3'), A_166) | ~m1_pre_topc('#skF_2', A_166) | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_166)))) | ~l1_pre_topc(A_166))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2303])).
% 4.82/1.89  tff(c_2698, plain, (![A_178]: (~v1_tops_2(u1_pre_topc('#skF_3'), A_178) | ~m1_pre_topc('#skF_2', A_178) | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_178)))) | ~l1_pre_topc(A_178))), inference(negUnitSimplification, [status(thm)], [c_1755, c_2329])).
% 4.82/1.89  tff(c_2704, plain, (~v1_tops_2(u1_pre_topc('#skF_3'), '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2140, c_2698])).
% 4.82/1.89  tff(c_2727, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_146, c_1915, c_2704])).
% 4.82/1.89  tff(c_2728, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(splitRight, [status(thm)], [c_1539])).
% 4.82/1.89  tff(c_2904, plain, (![A_187, B_188]: (r2_hidden(k6_subset_1(u1_struct_0(A_187), B_188), u1_pre_topc(A_187)) | ~r2_hidden(B_188, u1_pre_topc(A_187)) | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0(A_187))) | ~v3_tdlat_3(A_187) | ~l1_pre_topc(A_187))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.82/1.89  tff(c_2914, plain, (![B_188]: (r2_hidden(k6_subset_1(u1_struct_0('#skF_3'), B_188), u1_pre_topc('#skF_2')) | ~r2_hidden(B_188, u1_pre_topc('#skF_2')) | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v3_tdlat_3('#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_207, c_2904])).
% 4.82/1.89  tff(c_3663, plain, (![B_222]: (r2_hidden(k6_subset_1(u1_struct_0('#skF_3'), B_222), u1_pre_topc('#skF_3')) | ~r2_hidden(B_222, u1_pre_topc('#skF_3')) | ~m1_subset_1(B_222, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_207, c_2728, c_2728, c_2914])).
% 4.82/1.89  tff(c_32, plain, (![A_42]: (~r2_hidden(k6_subset_1(u1_struct_0(A_42), '#skF_1'(A_42)), u1_pre_topc(A_42)) | v3_tdlat_3(A_42) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.82/1.89  tff(c_3667, plain, (v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_3663, c_32])).
% 4.82/1.89  tff(c_3670, plain, (v3_tdlat_3('#skF_3') | ~r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3667])).
% 4.82/1.89  tff(c_3671, plain, (~r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_38, c_3670])).
% 4.82/1.89  tff(c_3672, plain, (~m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_3671])).
% 4.82/1.89  tff(c_3675, plain, (v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_3672])).
% 4.82/1.89  tff(c_3678, plain, (v3_tdlat_3('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3675])).
% 4.82/1.89  tff(c_3680, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_3678])).
% 4.82/1.89  tff(c_3681, plain, (~r2_hidden('#skF_1'('#skF_3'), u1_pre_topc('#skF_3'))), inference(splitRight, [status(thm)], [c_3671])).
% 4.82/1.89  tff(c_3685, plain, (v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34, c_3681])).
% 4.82/1.89  tff(c_3688, plain, (v3_tdlat_3('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3685])).
% 4.82/1.89  tff(c_3690, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_3688])).
% 4.82/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.89  
% 4.82/1.89  Inference rules
% 4.82/1.89  ----------------------
% 4.82/1.89  #Ref     : 0
% 4.82/1.89  #Sup     : 654
% 4.82/1.89  #Fact    : 0
% 4.82/1.89  #Define  : 0
% 4.82/1.89  #Split   : 8
% 4.82/1.89  #Chain   : 0
% 4.82/1.89  #Close   : 0
% 4.82/1.89  
% 4.82/1.89  Ordering : KBO
% 4.82/1.89  
% 4.82/1.89  Simplification rules
% 4.82/1.89  ----------------------
% 4.82/1.89  #Subsume      : 139
% 4.82/1.89  #Demod        : 1108
% 4.82/1.89  #Tautology    : 305
% 4.82/1.89  #SimpNegUnit  : 48
% 4.82/1.89  #BackRed      : 4
% 4.82/1.89  
% 4.82/1.89  #Partial instantiations: 0
% 4.82/1.89  #Strategies tried      : 1
% 4.82/1.89  
% 4.82/1.89  Timing (in seconds)
% 4.82/1.89  ----------------------
% 4.82/1.89  Preprocessing        : 0.33
% 4.82/1.89  Parsing              : 0.18
% 4.82/1.89  CNF conversion       : 0.02
% 4.82/1.89  Main loop            : 0.77
% 4.82/1.89  Inferencing          : 0.26
% 4.82/1.89  Reduction            : 0.25
% 4.82/1.89  Demodulation         : 0.17
% 4.82/1.89  BG Simplification    : 0.03
% 4.82/1.89  Subsumption          : 0.18
% 4.82/1.89  Abstraction          : 0.03
% 4.82/1.89  MUC search           : 0.00
% 4.82/1.90  Cooper               : 0.00
% 4.82/1.90  Total                : 1.15
% 4.82/1.90  Index Insertion      : 0.00
% 4.82/1.90  Index Deletion       : 0.00
% 4.82/1.90  Index Matching       : 0.00
% 4.82/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
