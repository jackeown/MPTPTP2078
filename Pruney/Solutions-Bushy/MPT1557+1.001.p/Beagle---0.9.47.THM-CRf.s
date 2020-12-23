%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1557+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:03 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 181 expanded)
%              Number of leaves         :   27 (  74 expanded)
%              Depth                    :   11
%              Number of atoms          :  208 ( 535 expanded)
%              Number of equality atoms :    1 (   6 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r1_lattice3 > r2_yellow_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_orders_2 > k2_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B,C] :
            ( ( r1_tarski(B,C)
              & r2_yellow_0(A,B)
              & r2_yellow_0(A,C) )
           => r1_orders_2(A,k2_yellow_0(A,C),k2_yellow_0(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_yellow_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k2_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_yellow_0(A,B)
           => ( C = k2_yellow_0(A,B)
            <=> ( r1_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r1_lattice3(A,B,D)
                     => r1_orders_2(A,D,C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_40,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_20,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(k2_yellow_0(A_25,B_26),u1_struct_0(A_25))
      | ~ l1_orders_2(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_38,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_22,plain,(
    ! [A_27,B_28] :
      ( r2_hidden(A_27,B_28)
      | v1_xboole_0(B_28)
      | ~ m1_subset_1(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(A_29,k1_zfmisc_1(B_30))
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_49,plain,(
    ! [C_47,B_48,A_49] :
      ( ~ v1_xboole_0(C_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(C_47))
      | ~ r2_hidden(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_53,plain,(
    ! [B_50,A_51,A_52] :
      ( ~ v1_xboole_0(B_50)
      | ~ r2_hidden(A_51,A_52)
      | ~ r1_tarski(A_52,B_50) ) ),
    inference(resolution,[status(thm)],[c_26,c_49])).

tff(c_65,plain,(
    ! [B_59,B_60,A_61] :
      ( ~ v1_xboole_0(B_59)
      | ~ r1_tarski(B_60,B_59)
      | v1_xboole_0(B_60)
      | ~ m1_subset_1(A_61,B_60) ) ),
    inference(resolution,[status(thm)],[c_22,c_53])).

tff(c_68,plain,(
    ! [A_61] :
      ( ~ v1_xboole_0('#skF_5')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(A_61,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_65])).

tff(c_69,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_34,plain,(
    r2_yellow_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_36,plain,(
    r2_yellow_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_166,plain,(
    ! [A_121,D_122,B_123] :
      ( r1_orders_2(A_121,D_122,k2_yellow_0(A_121,B_123))
      | ~ r1_lattice3(A_121,B_123,D_122)
      | ~ m1_subset_1(D_122,u1_struct_0(A_121))
      | ~ r2_yellow_0(A_121,B_123)
      | ~ m1_subset_1(k2_yellow_0(A_121,B_123),u1_struct_0(A_121))
      | ~ l1_orders_2(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_170,plain,(
    ! [A_124,D_125,B_126] :
      ( r1_orders_2(A_124,D_125,k2_yellow_0(A_124,B_126))
      | ~ r1_lattice3(A_124,B_126,D_125)
      | ~ m1_subset_1(D_125,u1_struct_0(A_124))
      | ~ r2_yellow_0(A_124,B_126)
      | ~ l1_orders_2(A_124) ) ),
    inference(resolution,[status(thm)],[c_20,c_166])).

tff(c_32,plain,(
    ~ r1_orders_2('#skF_3',k2_yellow_0('#skF_3','#skF_5'),k2_yellow_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_177,plain,
    ( ~ r1_lattice3('#skF_3','#skF_4',k2_yellow_0('#skF_3','#skF_5'))
    | ~ m1_subset_1(k2_yellow_0('#skF_3','#skF_5'),u1_struct_0('#skF_3'))
    | ~ r2_yellow_0('#skF_3','#skF_4')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_170,c_32])).

tff(c_181,plain,
    ( ~ r1_lattice3('#skF_3','#skF_4',k2_yellow_0('#skF_3','#skF_5'))
    | ~ m1_subset_1(k2_yellow_0('#skF_3','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_177])).

tff(c_182,plain,(
    ~ m1_subset_1(k2_yellow_0('#skF_3','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_185,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_182])).

tff(c_189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_185])).

tff(c_191,plain,(
    m1_subset_1(k2_yellow_0('#skF_3','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_70,plain,(
    ! [A_62,B_63,C_64] :
      ( r2_hidden('#skF_2'(A_62,B_63,C_64),B_63)
      | r1_lattice3(A_62,B_63,C_64)
      | ~ m1_subset_1(C_64,u1_struct_0(A_62))
      | ~ l1_orders_2(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_57,plain,(
    ! [A_53,C_54,B_55] :
      ( m1_subset_1(A_53,C_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(C_54))
      | ~ r2_hidden(A_53,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_60,plain,(
    ! [A_53,B_30,A_29] :
      ( m1_subset_1(A_53,B_30)
      | ~ r2_hidden(A_53,A_29)
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(resolution,[status(thm)],[c_26,c_57])).

tff(c_75,plain,(
    ! [A_62,B_63,C_64,B_30] :
      ( m1_subset_1('#skF_2'(A_62,B_63,C_64),B_30)
      | ~ r1_tarski(B_63,B_30)
      | r1_lattice3(A_62,B_63,C_64)
      | ~ m1_subset_1(C_64,u1_struct_0(A_62))
      | ~ l1_orders_2(A_62) ) ),
    inference(resolution,[status(thm)],[c_70,c_60])).

tff(c_87,plain,(
    ! [A_75,B_76] :
      ( r1_lattice3(A_75,B_76,k2_yellow_0(A_75,B_76))
      | ~ r2_yellow_0(A_75,B_76)
      | ~ m1_subset_1(k2_yellow_0(A_75,B_76),u1_struct_0(A_75))
      | ~ l1_orders_2(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_90,plain,(
    ! [A_25,B_26] :
      ( r1_lattice3(A_25,B_26,k2_yellow_0(A_25,B_26))
      | ~ r2_yellow_0(A_25,B_26)
      | ~ l1_orders_2(A_25) ) ),
    inference(resolution,[status(thm)],[c_20,c_87])).

tff(c_18,plain,(
    ! [A_13,B_20,C_21] :
      ( m1_subset_1('#skF_2'(A_13,B_20,C_21),u1_struct_0(A_13))
      | r1_lattice3(A_13,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_93,plain,(
    ! [A_82,C_83,D_84,B_85] :
      ( r1_orders_2(A_82,C_83,D_84)
      | ~ r2_hidden(D_84,B_85)
      | ~ m1_subset_1(D_84,u1_struct_0(A_82))
      | ~ r1_lattice3(A_82,B_85,C_83)
      | ~ m1_subset_1(C_83,u1_struct_0(A_82))
      | ~ l1_orders_2(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_134,plain,(
    ! [A_102,C_103,A_104,B_105] :
      ( r1_orders_2(A_102,C_103,A_104)
      | ~ m1_subset_1(A_104,u1_struct_0(A_102))
      | ~ r1_lattice3(A_102,B_105,C_103)
      | ~ m1_subset_1(C_103,u1_struct_0(A_102))
      | ~ l1_orders_2(A_102)
      | v1_xboole_0(B_105)
      | ~ m1_subset_1(A_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_22,c_93])).

tff(c_272,plain,(
    ! [C_169,B_166,C_165,B_167,A_168] :
      ( r1_orders_2(A_168,C_169,'#skF_2'(A_168,B_167,C_165))
      | ~ r1_lattice3(A_168,B_166,C_169)
      | ~ m1_subset_1(C_169,u1_struct_0(A_168))
      | v1_xboole_0(B_166)
      | ~ m1_subset_1('#skF_2'(A_168,B_167,C_165),B_166)
      | r1_lattice3(A_168,B_167,C_165)
      | ~ m1_subset_1(C_165,u1_struct_0(A_168))
      | ~ l1_orders_2(A_168) ) ),
    inference(resolution,[status(thm)],[c_18,c_134])).

tff(c_297,plain,(
    ! [A_172,B_173,B_174,C_175] :
      ( r1_orders_2(A_172,k2_yellow_0(A_172,B_173),'#skF_2'(A_172,B_174,C_175))
      | ~ m1_subset_1(k2_yellow_0(A_172,B_173),u1_struct_0(A_172))
      | v1_xboole_0(B_173)
      | ~ m1_subset_1('#skF_2'(A_172,B_174,C_175),B_173)
      | r1_lattice3(A_172,B_174,C_175)
      | ~ m1_subset_1(C_175,u1_struct_0(A_172))
      | ~ r2_yellow_0(A_172,B_173)
      | ~ l1_orders_2(A_172) ) ),
    inference(resolution,[status(thm)],[c_90,c_272])).

tff(c_14,plain,(
    ! [A_13,C_21,B_20] :
      ( ~ r1_orders_2(A_13,C_21,'#skF_2'(A_13,B_20,C_21))
      | r1_lattice3(A_13,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_303,plain,(
    ! [B_176,A_177,B_178] :
      ( v1_xboole_0(B_176)
      | ~ m1_subset_1('#skF_2'(A_177,B_178,k2_yellow_0(A_177,B_176)),B_176)
      | r1_lattice3(A_177,B_178,k2_yellow_0(A_177,B_176))
      | ~ m1_subset_1(k2_yellow_0(A_177,B_176),u1_struct_0(A_177))
      | ~ r2_yellow_0(A_177,B_176)
      | ~ l1_orders_2(A_177) ) ),
    inference(resolution,[status(thm)],[c_297,c_14])).

tff(c_319,plain,(
    ! [B_179,A_180,B_181] :
      ( v1_xboole_0(B_179)
      | ~ r2_yellow_0(A_180,B_179)
      | ~ r1_tarski(B_181,B_179)
      | r1_lattice3(A_180,B_181,k2_yellow_0(A_180,B_179))
      | ~ m1_subset_1(k2_yellow_0(A_180,B_179),u1_struct_0(A_180))
      | ~ l1_orders_2(A_180) ) ),
    inference(resolution,[status(thm)],[c_75,c_303])).

tff(c_321,plain,(
    ! [B_181] :
      ( v1_xboole_0('#skF_5')
      | ~ r2_yellow_0('#skF_3','#skF_5')
      | ~ r1_tarski(B_181,'#skF_5')
      | r1_lattice3('#skF_3',B_181,k2_yellow_0('#skF_3','#skF_5'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_191,c_319])).

tff(c_326,plain,(
    ! [B_181] :
      ( v1_xboole_0('#skF_5')
      | ~ r1_tarski(B_181,'#skF_5')
      | r1_lattice3('#skF_3',B_181,k2_yellow_0('#skF_3','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_321])).

tff(c_329,plain,(
    ! [B_182] :
      ( ~ r1_tarski(B_182,'#skF_5')
      | r1_lattice3('#skF_3',B_182,k2_yellow_0('#skF_3','#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_326])).

tff(c_190,plain,(
    ~ r1_lattice3('#skF_3','#skF_4',k2_yellow_0('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_339,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_329,c_190])).

tff(c_352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_339])).

tff(c_354,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_357,plain,(
    ! [A_184,B_185,C_186] :
      ( r2_hidden('#skF_2'(A_184,B_185,C_186),B_185)
      | r1_lattice3(A_184,B_185,C_186)
      | ~ m1_subset_1(C_186,u1_struct_0(A_184))
      | ~ l1_orders_2(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_52,plain,(
    ! [B_30,A_49,A_29] :
      ( ~ v1_xboole_0(B_30)
      | ~ r2_hidden(A_49,A_29)
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(resolution,[status(thm)],[c_26,c_49])).

tff(c_368,plain,(
    ! [B_190,B_191,A_192,C_193] :
      ( ~ v1_xboole_0(B_190)
      | ~ r1_tarski(B_191,B_190)
      | r1_lattice3(A_192,B_191,C_193)
      | ~ m1_subset_1(C_193,u1_struct_0(A_192))
      | ~ l1_orders_2(A_192) ) ),
    inference(resolution,[status(thm)],[c_357,c_52])).

tff(c_370,plain,(
    ! [A_192,C_193] :
      ( ~ v1_xboole_0('#skF_5')
      | r1_lattice3(A_192,'#skF_4',C_193)
      | ~ m1_subset_1(C_193,u1_struct_0(A_192))
      | ~ l1_orders_2(A_192) ) ),
    inference(resolution,[status(thm)],[c_38,c_368])).

tff(c_374,plain,(
    ! [A_194,C_195] :
      ( r1_lattice3(A_194,'#skF_4',C_195)
      | ~ m1_subset_1(C_195,u1_struct_0(A_194))
      | ~ l1_orders_2(A_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_370])).

tff(c_378,plain,(
    ! [A_25,B_26] :
      ( r1_lattice3(A_25,'#skF_4',k2_yellow_0(A_25,B_26))
      | ~ l1_orders_2(A_25) ) ),
    inference(resolution,[status(thm)],[c_20,c_374])).

tff(c_515,plain,(
    ! [A_267,D_268,B_269] :
      ( r1_orders_2(A_267,D_268,k2_yellow_0(A_267,B_269))
      | ~ r1_lattice3(A_267,B_269,D_268)
      | ~ m1_subset_1(D_268,u1_struct_0(A_267))
      | ~ r2_yellow_0(A_267,B_269)
      | ~ m1_subset_1(k2_yellow_0(A_267,B_269),u1_struct_0(A_267))
      | ~ l1_orders_2(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_519,plain,(
    ! [A_270,D_271,B_272] :
      ( r1_orders_2(A_270,D_271,k2_yellow_0(A_270,B_272))
      | ~ r1_lattice3(A_270,B_272,D_271)
      | ~ m1_subset_1(D_271,u1_struct_0(A_270))
      | ~ r2_yellow_0(A_270,B_272)
      | ~ l1_orders_2(A_270) ) ),
    inference(resolution,[status(thm)],[c_20,c_515])).

tff(c_526,plain,
    ( ~ r1_lattice3('#skF_3','#skF_4',k2_yellow_0('#skF_3','#skF_5'))
    | ~ m1_subset_1(k2_yellow_0('#skF_3','#skF_5'),u1_struct_0('#skF_3'))
    | ~ r2_yellow_0('#skF_3','#skF_4')
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_519,c_32])).

tff(c_530,plain,
    ( ~ r1_lattice3('#skF_3','#skF_4',k2_yellow_0('#skF_3','#skF_5'))
    | ~ m1_subset_1(k2_yellow_0('#skF_3','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_526])).

tff(c_531,plain,(
    ~ m1_subset_1(k2_yellow_0('#skF_3','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_530])).

tff(c_534,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_531])).

tff(c_538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_534])).

tff(c_539,plain,(
    ~ r1_lattice3('#skF_3','#skF_4',k2_yellow_0('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_530])).

tff(c_546,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_378,c_539])).

tff(c_553,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_546])).

%------------------------------------------------------------------------------
