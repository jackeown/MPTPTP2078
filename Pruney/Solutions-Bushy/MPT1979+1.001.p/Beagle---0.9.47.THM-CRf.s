%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1979+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:44 EST 2020

% Result     : Theorem 18.20s
% Output     : CNFRefutation 18.28s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 512 expanded)
%              Number of leaves         :   47 ( 209 expanded)
%              Depth                    :   41
%              Number of atoms          : 1014 (4288 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   26 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > v2_waybel_0 > v1_waybel_7 > v1_waybel_0 > v13_waybel_0 > v12_waybel_0 > r2_hidden > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_waybel_1 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_lattice3 > l1_orders_2 > k6_waybel_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_waybel_7,type,(
    v1_waybel_7: ( $i * $i ) > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(r1_subset_1,type,(
    r1_subset_1: ( $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(v2_waybel_1,type,(
    v2_waybel_1: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v12_waybel_0,type,(
    v12_waybel_0: ( $i * $i ) > $o )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k6_waybel_0,type,(
    k6_waybel_0: ( $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

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

tff(f_265,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v2_waybel_1(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_waybel_0(B,A)
              & v12_waybel_0(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ~ ( ~ r2_hidden(C,B)
                    & ! [D] :
                        ( ( ~ v1_xboole_0(D)
                          & v1_waybel_0(D,A)
                          & v12_waybel_0(D,A)
                          & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                       => ~ ( v1_waybel_7(D,A)
                            & r1_tarski(B,D)
                            & ~ r2_hidden(C,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_waybel_7)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v1_xboole_0(k6_waybel_0(A,B))
        & v2_waybel_0(k6_waybel_0(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_waybel_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k6_waybel_0(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_waybel_0)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_209,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_215,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_137,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k6_waybel_0(A,B))
              <=> r1_orders_2(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_waybel_0)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v12_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r1_orders_2(A,D,C) )
                     => r2_hidden(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_waybel_0)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v4_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => v13_waybel_0(k6_waybel_0(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_waybel_0)).

tff(f_191,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v2_waybel_1(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_waybel_0(B,A)
            & v12_waybel_0(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ! [C] :
              ( ( ~ v1_xboole_0(C)
                & v2_waybel_0(C,A)
                & v13_waybel_0(C,A)
                & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
             => ~ ( r1_subset_1(B,C)
                  & ! [D] :
                      ( ( ~ v1_xboole_0(D)
                        & v1_waybel_0(D,A)
                        & v12_waybel_0(D,A)
                        & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                     => ~ ( v1_waybel_7(D,A)
                          & r1_tarski(B,D)
                          & r1_subset_1(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_waybel_7)).

tff(c_74,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_76,plain,(
    v2_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_62,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_86,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_64,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_121,plain,(
    ! [A_102,B_103] :
      ( ~ v1_xboole_0(k6_waybel_0(A_102,B_103))
      | ~ m1_subset_1(B_103,u1_struct_0(A_102))
      | ~ l1_orders_2(A_102)
      | ~ v3_orders_2(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_127,plain,
    ( ~ v1_xboole_0(k6_waybel_0('#skF_5','#skF_7'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_121])).

tff(c_133,plain,
    ( ~ v1_xboole_0(k6_waybel_0('#skF_5','#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_74,c_127])).

tff(c_134,plain,(
    ~ v1_xboole_0(k6_waybel_0('#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_138,plain,(
    ! [A_107,B_108] :
      ( m1_subset_1(k6_waybel_0(A_107,B_108),k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ m1_subset_1(B_108,u1_struct_0(A_107))
      | ~ l1_orders_2(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_60,plain,(
    ! [D_81] :
      ( r2_hidden('#skF_7',D_81)
      | ~ r1_tarski('#skF_6',D_81)
      | ~ v1_waybel_7(D_81,'#skF_5')
      | ~ m1_subset_1(D_81,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v12_waybel_0(D_81,'#skF_5')
      | ~ v1_waybel_0(D_81,'#skF_5')
      | v1_xboole_0(D_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_142,plain,(
    ! [B_108] :
      ( r2_hidden('#skF_7',k6_waybel_0('#skF_5',B_108))
      | ~ r1_tarski('#skF_6',k6_waybel_0('#skF_5',B_108))
      | ~ v1_waybel_7(k6_waybel_0('#skF_5',B_108),'#skF_5')
      | ~ v12_waybel_0(k6_waybel_0('#skF_5',B_108),'#skF_5')
      | ~ v1_waybel_0(k6_waybel_0('#skF_5',B_108),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_108))
      | ~ m1_subset_1(B_108,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_138,c_60])).

tff(c_147,plain,(
    ! [B_108] :
      ( r2_hidden('#skF_7',k6_waybel_0('#skF_5',B_108))
      | ~ r1_tarski('#skF_6',k6_waybel_0('#skF_5',B_108))
      | ~ v1_waybel_7(k6_waybel_0('#skF_5',B_108),'#skF_5')
      | ~ v12_waybel_0(k6_waybel_0('#skF_5',B_108),'#skF_5')
      | ~ v1_waybel_0(k6_waybel_0('#skF_5',B_108),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_108))
      | ~ m1_subset_1(B_108,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_142])).

tff(c_184,plain,(
    v2_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v2_struct_0(A_1)
      | ~ v2_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_187,plain,
    ( ~ v2_lattice3('#skF_5')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_184,c_2])).

tff(c_191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_187])).

tff(c_193,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_247,plain,(
    ! [A_148,B_149,C_150] :
      ( r3_orders_2(A_148,B_149,B_149)
      | ~ m1_subset_1(C_150,u1_struct_0(A_148))
      | ~ m1_subset_1(B_149,u1_struct_0(A_148))
      | ~ l1_orders_2(A_148)
      | ~ v3_orders_2(A_148)
      | v2_struct_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_255,plain,(
    ! [B_149] :
      ( r3_orders_2('#skF_5',B_149,B_149)
      | ~ m1_subset_1(B_149,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_247])).

tff(c_264,plain,(
    ! [B_149] :
      ( r3_orders_2('#skF_5',B_149,B_149)
      | ~ m1_subset_1(B_149,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_74,c_255])).

tff(c_266,plain,(
    ! [B_151] :
      ( r3_orders_2('#skF_5',B_151,B_151)
      | ~ m1_subset_1(B_151,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_264])).

tff(c_284,plain,(
    r3_orders_2('#skF_5','#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_266])).

tff(c_501,plain,(
    ! [A_187,B_188,C_189] :
      ( r1_orders_2(A_187,B_188,C_189)
      | ~ r3_orders_2(A_187,B_188,C_189)
      | ~ m1_subset_1(C_189,u1_struct_0(A_187))
      | ~ m1_subset_1(B_188,u1_struct_0(A_187))
      | ~ l1_orders_2(A_187)
      | ~ v3_orders_2(A_187)
      | v2_struct_0(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_519,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_284,c_501])).

tff(c_554,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_7')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_74,c_64,c_519])).

tff(c_555,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_554])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_68,plain,(
    v12_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_56,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_4'(A_62,B_63),A_62)
      | r1_xboole_0(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_54,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_4'(A_62,B_63),B_63)
      | r1_xboole_0(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_58,plain,(
    ! [A_67,C_69,B_68] :
      ( m1_subset_1(A_67,C_69)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(C_69))
      | ~ r2_hidden(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_235,plain,(
    ! [A_143,A_144,B_145] :
      ( m1_subset_1(A_143,u1_struct_0(A_144))
      | ~ r2_hidden(A_143,k6_waybel_0(A_144,B_145))
      | ~ m1_subset_1(B_145,u1_struct_0(A_144))
      | ~ l1_orders_2(A_144)
      | v2_struct_0(A_144) ) ),
    inference(resolution,[status(thm)],[c_138,c_58])).

tff(c_244,plain,(
    ! [A_62,A_144,B_145] :
      ( m1_subset_1('#skF_4'(A_62,k6_waybel_0(A_144,B_145)),u1_struct_0(A_144))
      | ~ m1_subset_1(B_145,u1_struct_0(A_144))
      | ~ l1_orders_2(A_144)
      | v2_struct_0(A_144)
      | r1_xboole_0(A_62,k6_waybel_0(A_144,B_145)) ) ),
    inference(resolution,[status(thm)],[c_54,c_235])).

tff(c_95,plain,(
    ! [A_92,C_93,B_94] :
      ( m1_subset_1(A_92,C_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(C_93))
      | ~ r2_hidden(A_92,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_98,plain,(
    ! [A_92] :
      ( m1_subset_1(A_92,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_92,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_66,c_95])).

tff(c_325,plain,(
    ! [A_162,B_163,C_164] :
      ( r1_orders_2(A_162,B_163,C_164)
      | ~ r2_hidden(C_164,k6_waybel_0(A_162,B_163))
      | ~ m1_subset_1(C_164,u1_struct_0(A_162))
      | ~ m1_subset_1(B_163,u1_struct_0(A_162))
      | ~ l1_orders_2(A_162)
      | v2_struct_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_879,plain,(
    ! [A_251,B_252,A_253] :
      ( r1_orders_2(A_251,B_252,'#skF_4'(A_253,k6_waybel_0(A_251,B_252)))
      | ~ m1_subset_1('#skF_4'(A_253,k6_waybel_0(A_251,B_252)),u1_struct_0(A_251))
      | ~ m1_subset_1(B_252,u1_struct_0(A_251))
      | ~ l1_orders_2(A_251)
      | v2_struct_0(A_251)
      | r1_xboole_0(A_253,k6_waybel_0(A_251,B_252)) ) ),
    inference(resolution,[status(thm)],[c_54,c_325])).

tff(c_887,plain,(
    ! [B_252,A_253] :
      ( r1_orders_2('#skF_5',B_252,'#skF_4'(A_253,k6_waybel_0('#skF_5',B_252)))
      | ~ m1_subset_1(B_252,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | r1_xboole_0(A_253,k6_waybel_0('#skF_5',B_252))
      | ~ r2_hidden('#skF_4'(A_253,k6_waybel_0('#skF_5',B_252)),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_98,c_879])).

tff(c_892,plain,(
    ! [B_252,A_253] :
      ( r1_orders_2('#skF_5',B_252,'#skF_4'(A_253,k6_waybel_0('#skF_5',B_252)))
      | ~ m1_subset_1(B_252,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | r1_xboole_0(A_253,k6_waybel_0('#skF_5',B_252))
      | ~ r2_hidden('#skF_4'(A_253,k6_waybel_0('#skF_5',B_252)),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_887])).

tff(c_908,plain,(
    ! [B_260,A_261] :
      ( r1_orders_2('#skF_5',B_260,'#skF_4'(A_261,k6_waybel_0('#skF_5',B_260)))
      | ~ m1_subset_1(B_260,u1_struct_0('#skF_5'))
      | r1_xboole_0(A_261,k6_waybel_0('#skF_5',B_260))
      | ~ r2_hidden('#skF_4'(A_261,k6_waybel_0('#skF_5',B_260)),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_892])).

tff(c_4,plain,(
    ! [D_25,B_16,A_2,C_23] :
      ( r2_hidden(D_25,B_16)
      | ~ r1_orders_2(A_2,D_25,C_23)
      | ~ r2_hidden(C_23,B_16)
      | ~ m1_subset_1(D_25,u1_struct_0(A_2))
      | ~ m1_subset_1(C_23,u1_struct_0(A_2))
      | ~ v12_waybel_0(B_16,A_2)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_910,plain,(
    ! [B_260,B_16,A_261] :
      ( r2_hidden(B_260,B_16)
      | ~ r2_hidden('#skF_4'(A_261,k6_waybel_0('#skF_5',B_260)),B_16)
      | ~ m1_subset_1('#skF_4'(A_261,k6_waybel_0('#skF_5',B_260)),u1_struct_0('#skF_5'))
      | ~ v12_waybel_0(B_16,'#skF_5')
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ m1_subset_1(B_260,u1_struct_0('#skF_5'))
      | r1_xboole_0(A_261,k6_waybel_0('#skF_5',B_260))
      | ~ r2_hidden('#skF_4'(A_261,k6_waybel_0('#skF_5',B_260)),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_908,c_4])).

tff(c_1079,plain,(
    ! [B_311,B_312,A_313] :
      ( r2_hidden(B_311,B_312)
      | ~ r2_hidden('#skF_4'(A_313,k6_waybel_0('#skF_5',B_311)),B_312)
      | ~ m1_subset_1('#skF_4'(A_313,k6_waybel_0('#skF_5',B_311)),u1_struct_0('#skF_5'))
      | ~ v12_waybel_0(B_312,'#skF_5')
      | ~ m1_subset_1(B_312,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_311,u1_struct_0('#skF_5'))
      | r1_xboole_0(A_313,k6_waybel_0('#skF_5',B_311))
      | ~ r2_hidden('#skF_4'(A_313,k6_waybel_0('#skF_5',B_311)),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_910])).

tff(c_1647,plain,(
    ! [B_443,A_444] :
      ( r2_hidden(B_443,A_444)
      | ~ m1_subset_1('#skF_4'(A_444,k6_waybel_0('#skF_5',B_443)),u1_struct_0('#skF_5'))
      | ~ v12_waybel_0(A_444,'#skF_5')
      | ~ m1_subset_1(A_444,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_443,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_4'(A_444,k6_waybel_0('#skF_5',B_443)),'#skF_6')
      | r1_xboole_0(A_444,k6_waybel_0('#skF_5',B_443)) ) ),
    inference(resolution,[status(thm)],[c_56,c_1079])).

tff(c_1655,plain,(
    ! [B_145,A_62] :
      ( r2_hidden(B_145,A_62)
      | ~ v12_waybel_0(A_62,'#skF_5')
      | ~ m1_subset_1(A_62,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_hidden('#skF_4'(A_62,k6_waybel_0('#skF_5',B_145)),'#skF_6')
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | r1_xboole_0(A_62,k6_waybel_0('#skF_5',B_145)) ) ),
    inference(resolution,[status(thm)],[c_244,c_1647])).

tff(c_1665,plain,(
    ! [B_145,A_62] :
      ( r2_hidden(B_145,A_62)
      | ~ v12_waybel_0(A_62,'#skF_5')
      | ~ m1_subset_1(A_62,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_hidden('#skF_4'(A_62,k6_waybel_0('#skF_5',B_145)),'#skF_6')
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | r1_xboole_0(A_62,k6_waybel_0('#skF_5',B_145)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1655])).

tff(c_1668,plain,(
    ! [B_445,A_446] :
      ( r2_hidden(B_445,A_446)
      | ~ v12_waybel_0(A_446,'#skF_5')
      | ~ m1_subset_1(A_446,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_hidden('#skF_4'(A_446,k6_waybel_0('#skF_5',B_445)),'#skF_6')
      | ~ m1_subset_1(B_445,u1_struct_0('#skF_5'))
      | r1_xboole_0(A_446,k6_waybel_0('#skF_5',B_445)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_1665])).

tff(c_1672,plain,(
    ! [B_445] :
      ( r2_hidden(B_445,'#skF_6')
      | ~ v12_waybel_0('#skF_6','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_445,u1_struct_0('#skF_5'))
      | r1_xboole_0('#skF_6',k6_waybel_0('#skF_5',B_445)) ) ),
    inference(resolution,[status(thm)],[c_56,c_1668])).

tff(c_1676,plain,(
    ! [B_447] :
      ( r2_hidden(B_447,'#skF_6')
      | ~ m1_subset_1(B_447,u1_struct_0('#skF_5'))
      | r1_xboole_0('#skF_6',k6_waybel_0('#skF_5',B_447)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_1672])).

tff(c_24,plain,(
    ! [A_33,B_34] :
      ( r1_subset_1(A_33,B_34)
      | ~ r1_xboole_0(A_33,B_34)
      | v1_xboole_0(B_34)
      | v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1679,plain,(
    ! [B_447] :
      ( r1_subset_1('#skF_6',k6_waybel_0('#skF_5',B_447))
      | v1_xboole_0(k6_waybel_0('#skF_5',B_447))
      | v1_xboole_0('#skF_6')
      | r2_hidden(B_447,'#skF_6')
      | ~ m1_subset_1(B_447,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1676,c_24])).

tff(c_1684,plain,(
    ! [B_447] :
      ( r1_subset_1('#skF_6',k6_waybel_0('#skF_5',B_447))
      | v1_xboole_0(k6_waybel_0('#skF_5',B_447))
      | r2_hidden(B_447,'#skF_6')
      | ~ m1_subset_1(B_447,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1679])).

tff(c_34,plain,(
    ! [C_47,A_41,B_45] :
      ( r2_hidden(C_47,k6_waybel_0(A_41,B_45))
      | ~ r1_orders_2(A_41,B_45,C_47)
      | ~ m1_subset_1(C_47,u1_struct_0(A_41))
      | ~ m1_subset_1(B_45,u1_struct_0(A_41))
      | ~ l1_orders_2(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_84,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_18,plain,(
    ! [A_29,B_30] :
      ( v13_waybel_0(k6_waybel_0(A_29,B_30),A_29)
      | ~ m1_subset_1(B_30,u1_struct_0(A_29))
      | ~ l1_orders_2(A_29)
      | ~ v4_orders_2(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    ! [A_31,B_32] :
      ( v2_waybel_0(k6_waybel_0(A_31,B_32),A_31)
      | ~ m1_subset_1(B_32,u1_struct_0(A_31))
      | ~ l1_orders_2(A_31)
      | ~ v3_orders_2(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_16,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(k6_waybel_0(A_27,B_28),k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ m1_subset_1(B_28,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_82,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_80,plain,(
    v2_waybel_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_78,plain,(
    v1_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_70,plain,(
    v1_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_265])).

tff(c_854,plain,(
    ! [B_244,A_245,C_246] :
      ( r1_tarski(B_244,'#skF_3'(A_245,B_244,C_246))
      | ~ r1_subset_1(B_244,C_246)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ v13_waybel_0(C_246,A_245)
      | ~ v2_waybel_0(C_246,A_245)
      | v1_xboole_0(C_246)
      | ~ m1_subset_1(B_244,k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ v12_waybel_0(B_244,A_245)
      | ~ v1_waybel_0(B_244,A_245)
      | v1_xboole_0(B_244)
      | ~ l1_orders_2(A_245)
      | ~ v2_lattice3(A_245)
      | ~ v1_lattice3(A_245)
      | ~ v2_waybel_1(A_245)
      | ~ v5_orders_2(A_245)
      | ~ v4_orders_2(A_245)
      | ~ v3_orders_2(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_859,plain,(
    ! [B_244,A_27,B_28] :
      ( r1_tarski(B_244,'#skF_3'(A_27,B_244,k6_waybel_0(A_27,B_28)))
      | ~ r1_subset_1(B_244,k6_waybel_0(A_27,B_28))
      | ~ v13_waybel_0(k6_waybel_0(A_27,B_28),A_27)
      | ~ v2_waybel_0(k6_waybel_0(A_27,B_28),A_27)
      | v1_xboole_0(k6_waybel_0(A_27,B_28))
      | ~ m1_subset_1(B_244,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ v12_waybel_0(B_244,A_27)
      | ~ v1_waybel_0(B_244,A_27)
      | v1_xboole_0(B_244)
      | ~ v2_lattice3(A_27)
      | ~ v1_lattice3(A_27)
      | ~ v2_waybel_1(A_27)
      | ~ v5_orders_2(A_27)
      | ~ v4_orders_2(A_27)
      | ~ v3_orders_2(A_27)
      | ~ m1_subset_1(B_28,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27)
      | v2_struct_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_16,c_854])).

tff(c_898,plain,(
    ! [A_257,B_258,C_259] :
      ( r1_subset_1('#skF_3'(A_257,B_258,C_259),C_259)
      | ~ r1_subset_1(B_258,C_259)
      | ~ m1_subset_1(C_259,k1_zfmisc_1(u1_struct_0(A_257)))
      | ~ v13_waybel_0(C_259,A_257)
      | ~ v2_waybel_0(C_259,A_257)
      | v1_xboole_0(C_259)
      | ~ m1_subset_1(B_258,k1_zfmisc_1(u1_struct_0(A_257)))
      | ~ v12_waybel_0(B_258,A_257)
      | ~ v1_waybel_0(B_258,A_257)
      | v1_xboole_0(B_258)
      | ~ l1_orders_2(A_257)
      | ~ v2_lattice3(A_257)
      | ~ v1_lattice3(A_257)
      | ~ v2_waybel_1(A_257)
      | ~ v5_orders_2(A_257)
      | ~ v4_orders_2(A_257)
      | ~ v3_orders_2(A_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_903,plain,(
    ! [A_27,B_258,B_28] :
      ( r1_subset_1('#skF_3'(A_27,B_258,k6_waybel_0(A_27,B_28)),k6_waybel_0(A_27,B_28))
      | ~ r1_subset_1(B_258,k6_waybel_0(A_27,B_28))
      | ~ v13_waybel_0(k6_waybel_0(A_27,B_28),A_27)
      | ~ v2_waybel_0(k6_waybel_0(A_27,B_28),A_27)
      | v1_xboole_0(k6_waybel_0(A_27,B_28))
      | ~ m1_subset_1(B_258,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ v12_waybel_0(B_258,A_27)
      | ~ v1_waybel_0(B_258,A_27)
      | v1_xboole_0(B_258)
      | ~ v2_lattice3(A_27)
      | ~ v1_lattice3(A_27)
      | ~ v2_waybel_1(A_27)
      | ~ v5_orders_2(A_27)
      | ~ v4_orders_2(A_27)
      | ~ v3_orders_2(A_27)
      | ~ m1_subset_1(B_28,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27)
      | v2_struct_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_16,c_898])).

tff(c_1045,plain,(
    ! [A_299,B_300,C_301] :
      ( v12_waybel_0('#skF_3'(A_299,B_300,C_301),A_299)
      | ~ r1_subset_1(B_300,C_301)
      | ~ m1_subset_1(C_301,k1_zfmisc_1(u1_struct_0(A_299)))
      | ~ v13_waybel_0(C_301,A_299)
      | ~ v2_waybel_0(C_301,A_299)
      | v1_xboole_0(C_301)
      | ~ m1_subset_1(B_300,k1_zfmisc_1(u1_struct_0(A_299)))
      | ~ v12_waybel_0(B_300,A_299)
      | ~ v1_waybel_0(B_300,A_299)
      | v1_xboole_0(B_300)
      | ~ l1_orders_2(A_299)
      | ~ v2_lattice3(A_299)
      | ~ v1_lattice3(A_299)
      | ~ v2_waybel_1(A_299)
      | ~ v5_orders_2(A_299)
      | ~ v4_orders_2(A_299)
      | ~ v3_orders_2(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1050,plain,(
    ! [A_27,B_300,B_28] :
      ( v12_waybel_0('#skF_3'(A_27,B_300,k6_waybel_0(A_27,B_28)),A_27)
      | ~ r1_subset_1(B_300,k6_waybel_0(A_27,B_28))
      | ~ v13_waybel_0(k6_waybel_0(A_27,B_28),A_27)
      | ~ v2_waybel_0(k6_waybel_0(A_27,B_28),A_27)
      | v1_xboole_0(k6_waybel_0(A_27,B_28))
      | ~ m1_subset_1(B_300,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ v12_waybel_0(B_300,A_27)
      | ~ v1_waybel_0(B_300,A_27)
      | v1_xboole_0(B_300)
      | ~ v2_lattice3(A_27)
      | ~ v1_lattice3(A_27)
      | ~ v2_waybel_1(A_27)
      | ~ v5_orders_2(A_27)
      | ~ v4_orders_2(A_27)
      | ~ v3_orders_2(A_27)
      | ~ m1_subset_1(B_28,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27)
      | v2_struct_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_16,c_1045])).

tff(c_964,plain,(
    ! [A_275,B_276,C_277] :
      ( v1_waybel_0('#skF_3'(A_275,B_276,C_277),A_275)
      | ~ r1_subset_1(B_276,C_277)
      | ~ m1_subset_1(C_277,k1_zfmisc_1(u1_struct_0(A_275)))
      | ~ v13_waybel_0(C_277,A_275)
      | ~ v2_waybel_0(C_277,A_275)
      | v1_xboole_0(C_277)
      | ~ m1_subset_1(B_276,k1_zfmisc_1(u1_struct_0(A_275)))
      | ~ v12_waybel_0(B_276,A_275)
      | ~ v1_waybel_0(B_276,A_275)
      | v1_xboole_0(B_276)
      | ~ l1_orders_2(A_275)
      | ~ v2_lattice3(A_275)
      | ~ v1_lattice3(A_275)
      | ~ v2_waybel_1(A_275)
      | ~ v5_orders_2(A_275)
      | ~ v4_orders_2(A_275)
      | ~ v3_orders_2(A_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_969,plain,(
    ! [A_27,B_276,B_28] :
      ( v1_waybel_0('#skF_3'(A_27,B_276,k6_waybel_0(A_27,B_28)),A_27)
      | ~ r1_subset_1(B_276,k6_waybel_0(A_27,B_28))
      | ~ v13_waybel_0(k6_waybel_0(A_27,B_28),A_27)
      | ~ v2_waybel_0(k6_waybel_0(A_27,B_28),A_27)
      | v1_xboole_0(k6_waybel_0(A_27,B_28))
      | ~ m1_subset_1(B_276,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ v12_waybel_0(B_276,A_27)
      | ~ v1_waybel_0(B_276,A_27)
      | v1_xboole_0(B_276)
      | ~ v2_lattice3(A_27)
      | ~ v1_lattice3(A_27)
      | ~ v2_waybel_1(A_27)
      | ~ v5_orders_2(A_27)
      | ~ v4_orders_2(A_27)
      | ~ v3_orders_2(A_27)
      | ~ m1_subset_1(B_28,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27)
      | v2_struct_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_16,c_964])).

tff(c_1113,plain,(
    ! [A_324,B_325,C_326] :
      ( v1_waybel_7('#skF_3'(A_324,B_325,C_326),A_324)
      | ~ r1_subset_1(B_325,C_326)
      | ~ m1_subset_1(C_326,k1_zfmisc_1(u1_struct_0(A_324)))
      | ~ v13_waybel_0(C_326,A_324)
      | ~ v2_waybel_0(C_326,A_324)
      | v1_xboole_0(C_326)
      | ~ m1_subset_1(B_325,k1_zfmisc_1(u1_struct_0(A_324)))
      | ~ v12_waybel_0(B_325,A_324)
      | ~ v1_waybel_0(B_325,A_324)
      | v1_xboole_0(B_325)
      | ~ l1_orders_2(A_324)
      | ~ v2_lattice3(A_324)
      | ~ v1_lattice3(A_324)
      | ~ v2_waybel_1(A_324)
      | ~ v5_orders_2(A_324)
      | ~ v4_orders_2(A_324)
      | ~ v3_orders_2(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_2058,plain,(
    ! [A_497,B_498,B_499] :
      ( v1_waybel_7('#skF_3'(A_497,B_498,k6_waybel_0(A_497,B_499)),A_497)
      | ~ r1_subset_1(B_498,k6_waybel_0(A_497,B_499))
      | ~ v13_waybel_0(k6_waybel_0(A_497,B_499),A_497)
      | ~ v2_waybel_0(k6_waybel_0(A_497,B_499),A_497)
      | v1_xboole_0(k6_waybel_0(A_497,B_499))
      | ~ m1_subset_1(B_498,k1_zfmisc_1(u1_struct_0(A_497)))
      | ~ v12_waybel_0(B_498,A_497)
      | ~ v1_waybel_0(B_498,A_497)
      | v1_xboole_0(B_498)
      | ~ v2_lattice3(A_497)
      | ~ v1_lattice3(A_497)
      | ~ v2_waybel_1(A_497)
      | ~ v5_orders_2(A_497)
      | ~ v4_orders_2(A_497)
      | ~ v3_orders_2(A_497)
      | ~ m1_subset_1(B_499,u1_struct_0(A_497))
      | ~ l1_orders_2(A_497)
      | v2_struct_0(A_497) ) ),
    inference(resolution,[status(thm)],[c_16,c_1113])).

tff(c_1257,plain,(
    ! [A_357,B_358,C_359] :
      ( m1_subset_1('#skF_3'(A_357,B_358,C_359),k1_zfmisc_1(u1_struct_0(A_357)))
      | ~ r1_subset_1(B_358,C_359)
      | ~ m1_subset_1(C_359,k1_zfmisc_1(u1_struct_0(A_357)))
      | ~ v13_waybel_0(C_359,A_357)
      | ~ v2_waybel_0(C_359,A_357)
      | v1_xboole_0(C_359)
      | ~ m1_subset_1(B_358,k1_zfmisc_1(u1_struct_0(A_357)))
      | ~ v12_waybel_0(B_358,A_357)
      | ~ v1_waybel_0(B_358,A_357)
      | v1_xboole_0(B_358)
      | ~ l1_orders_2(A_357)
      | ~ v2_lattice3(A_357)
      | ~ v1_lattice3(A_357)
      | ~ v2_waybel_1(A_357)
      | ~ v5_orders_2(A_357)
      | ~ v4_orders_2(A_357)
      | ~ v3_orders_2(A_357) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1295,plain,(
    ! [B_358,C_359] :
      ( r2_hidden('#skF_7','#skF_3'('#skF_5',B_358,C_359))
      | ~ r1_tarski('#skF_6','#skF_3'('#skF_5',B_358,C_359))
      | ~ v1_waybel_7('#skF_3'('#skF_5',B_358,C_359),'#skF_5')
      | ~ v12_waybel_0('#skF_3'('#skF_5',B_358,C_359),'#skF_5')
      | ~ v1_waybel_0('#skF_3'('#skF_5',B_358,C_359),'#skF_5')
      | v1_xboole_0('#skF_3'('#skF_5',B_358,C_359))
      | ~ r1_subset_1(B_358,C_359)
      | ~ m1_subset_1(C_359,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v13_waybel_0(C_359,'#skF_5')
      | ~ v2_waybel_0(C_359,'#skF_5')
      | v1_xboole_0(C_359)
      | ~ m1_subset_1(B_358,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v12_waybel_0(B_358,'#skF_5')
      | ~ v1_waybel_0(B_358,'#skF_5')
      | v1_xboole_0(B_358)
      | ~ l1_orders_2('#skF_5')
      | ~ v2_lattice3('#skF_5')
      | ~ v1_lattice3('#skF_5')
      | ~ v2_waybel_1('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1257,c_60])).

tff(c_1322,plain,(
    ! [B_358,C_359] :
      ( r2_hidden('#skF_7','#skF_3'('#skF_5',B_358,C_359))
      | ~ r1_tarski('#skF_6','#skF_3'('#skF_5',B_358,C_359))
      | ~ v1_waybel_7('#skF_3'('#skF_5',B_358,C_359),'#skF_5')
      | ~ v12_waybel_0('#skF_3'('#skF_5',B_358,C_359),'#skF_5')
      | ~ v1_waybel_0('#skF_3'('#skF_5',B_358,C_359),'#skF_5')
      | v1_xboole_0('#skF_3'('#skF_5',B_358,C_359))
      | ~ r1_subset_1(B_358,C_359)
      | ~ m1_subset_1(C_359,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v13_waybel_0(C_359,'#skF_5')
      | ~ v2_waybel_0(C_359,'#skF_5')
      | v1_xboole_0(C_359)
      | ~ m1_subset_1(B_358,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v12_waybel_0(B_358,'#skF_5')
      | ~ v1_waybel_0(B_358,'#skF_5')
      | v1_xboole_0(B_358) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_80,c_78,c_76,c_74,c_1295])).

tff(c_2061,plain,(
    ! [B_498,B_499] :
      ( r2_hidden('#skF_7','#skF_3'('#skF_5',B_498,k6_waybel_0('#skF_5',B_499)))
      | ~ r1_tarski('#skF_6','#skF_3'('#skF_5',B_498,k6_waybel_0('#skF_5',B_499)))
      | ~ v12_waybel_0('#skF_3'('#skF_5',B_498,k6_waybel_0('#skF_5',B_499)),'#skF_5')
      | ~ v1_waybel_0('#skF_3'('#skF_5',B_498,k6_waybel_0('#skF_5',B_499)),'#skF_5')
      | v1_xboole_0('#skF_3'('#skF_5',B_498,k6_waybel_0('#skF_5',B_499)))
      | ~ m1_subset_1(k6_waybel_0('#skF_5',B_499),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_subset_1(B_498,k6_waybel_0('#skF_5',B_499))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_499),'#skF_5')
      | ~ v2_waybel_0(k6_waybel_0('#skF_5',B_499),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_499))
      | ~ m1_subset_1(B_498,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v12_waybel_0(B_498,'#skF_5')
      | ~ v1_waybel_0(B_498,'#skF_5')
      | v1_xboole_0(B_498)
      | ~ v2_lattice3('#skF_5')
      | ~ v1_lattice3('#skF_5')
      | ~ v2_waybel_1('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | ~ m1_subset_1(B_499,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2058,c_1322])).

tff(c_2064,plain,(
    ! [B_498,B_499] :
      ( r2_hidden('#skF_7','#skF_3'('#skF_5',B_498,k6_waybel_0('#skF_5',B_499)))
      | ~ r1_tarski('#skF_6','#skF_3'('#skF_5',B_498,k6_waybel_0('#skF_5',B_499)))
      | ~ v12_waybel_0('#skF_3'('#skF_5',B_498,k6_waybel_0('#skF_5',B_499)),'#skF_5')
      | ~ v1_waybel_0('#skF_3'('#skF_5',B_498,k6_waybel_0('#skF_5',B_499)),'#skF_5')
      | v1_xboole_0('#skF_3'('#skF_5',B_498,k6_waybel_0('#skF_5',B_499)))
      | ~ m1_subset_1(k6_waybel_0('#skF_5',B_499),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_subset_1(B_498,k6_waybel_0('#skF_5',B_499))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_499),'#skF_5')
      | ~ v2_waybel_0(k6_waybel_0('#skF_5',B_499),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_499))
      | ~ m1_subset_1(B_498,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v12_waybel_0(B_498,'#skF_5')
      | ~ v1_waybel_0(B_498,'#skF_5')
      | v1_xboole_0(B_498)
      | ~ m1_subset_1(B_499,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_86,c_84,c_82,c_80,c_78,c_76,c_2061])).

tff(c_4068,plain,(
    ! [B_775,B_776] :
      ( r2_hidden('#skF_7','#skF_3'('#skF_5',B_775,k6_waybel_0('#skF_5',B_776)))
      | ~ r1_tarski('#skF_6','#skF_3'('#skF_5',B_775,k6_waybel_0('#skF_5',B_776)))
      | ~ v12_waybel_0('#skF_3'('#skF_5',B_775,k6_waybel_0('#skF_5',B_776)),'#skF_5')
      | ~ v1_waybel_0('#skF_3'('#skF_5',B_775,k6_waybel_0('#skF_5',B_776)),'#skF_5')
      | v1_xboole_0('#skF_3'('#skF_5',B_775,k6_waybel_0('#skF_5',B_776)))
      | ~ m1_subset_1(k6_waybel_0('#skF_5',B_776),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_subset_1(B_775,k6_waybel_0('#skF_5',B_776))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_776),'#skF_5')
      | ~ v2_waybel_0(k6_waybel_0('#skF_5',B_776),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_776))
      | ~ m1_subset_1(B_775,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v12_waybel_0(B_775,'#skF_5')
      | ~ v1_waybel_0(B_775,'#skF_5')
      | v1_xboole_0(B_775)
      | ~ m1_subset_1(B_776,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_2064])).

tff(c_4071,plain,(
    ! [B_276,B_28] :
      ( r2_hidden('#skF_7','#skF_3'('#skF_5',B_276,k6_waybel_0('#skF_5',B_28)))
      | ~ r1_tarski('#skF_6','#skF_3'('#skF_5',B_276,k6_waybel_0('#skF_5',B_28)))
      | ~ v12_waybel_0('#skF_3'('#skF_5',B_276,k6_waybel_0('#skF_5',B_28)),'#skF_5')
      | v1_xboole_0('#skF_3'('#skF_5',B_276,k6_waybel_0('#skF_5',B_28)))
      | ~ m1_subset_1(k6_waybel_0('#skF_5',B_28),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_subset_1(B_276,k6_waybel_0('#skF_5',B_28))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_28),'#skF_5')
      | ~ v2_waybel_0(k6_waybel_0('#skF_5',B_28),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_28))
      | ~ m1_subset_1(B_276,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v12_waybel_0(B_276,'#skF_5')
      | ~ v1_waybel_0(B_276,'#skF_5')
      | v1_xboole_0(B_276)
      | ~ v2_lattice3('#skF_5')
      | ~ v1_lattice3('#skF_5')
      | ~ v2_waybel_1('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | ~ m1_subset_1(B_28,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_969,c_4068])).

tff(c_4074,plain,(
    ! [B_276,B_28] :
      ( r2_hidden('#skF_7','#skF_3'('#skF_5',B_276,k6_waybel_0('#skF_5',B_28)))
      | ~ r1_tarski('#skF_6','#skF_3'('#skF_5',B_276,k6_waybel_0('#skF_5',B_28)))
      | ~ v12_waybel_0('#skF_3'('#skF_5',B_276,k6_waybel_0('#skF_5',B_28)),'#skF_5')
      | v1_xboole_0('#skF_3'('#skF_5',B_276,k6_waybel_0('#skF_5',B_28)))
      | ~ m1_subset_1(k6_waybel_0('#skF_5',B_28),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_subset_1(B_276,k6_waybel_0('#skF_5',B_28))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_28),'#skF_5')
      | ~ v2_waybel_0(k6_waybel_0('#skF_5',B_28),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_28))
      | ~ m1_subset_1(B_276,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v12_waybel_0(B_276,'#skF_5')
      | ~ v1_waybel_0(B_276,'#skF_5')
      | v1_xboole_0(B_276)
      | ~ m1_subset_1(B_28,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_86,c_84,c_82,c_80,c_78,c_76,c_4071])).

tff(c_9842,plain,(
    ! [B_1306,B_1307] :
      ( r2_hidden('#skF_7','#skF_3'('#skF_5',B_1306,k6_waybel_0('#skF_5',B_1307)))
      | ~ r1_tarski('#skF_6','#skF_3'('#skF_5',B_1306,k6_waybel_0('#skF_5',B_1307)))
      | ~ v12_waybel_0('#skF_3'('#skF_5',B_1306,k6_waybel_0('#skF_5',B_1307)),'#skF_5')
      | v1_xboole_0('#skF_3'('#skF_5',B_1306,k6_waybel_0('#skF_5',B_1307)))
      | ~ m1_subset_1(k6_waybel_0('#skF_5',B_1307),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_subset_1(B_1306,k6_waybel_0('#skF_5',B_1307))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_1307),'#skF_5')
      | ~ v2_waybel_0(k6_waybel_0('#skF_5',B_1307),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_1307))
      | ~ m1_subset_1(B_1306,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v12_waybel_0(B_1306,'#skF_5')
      | ~ v1_waybel_0(B_1306,'#skF_5')
      | v1_xboole_0(B_1306)
      | ~ m1_subset_1(B_1307,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_4074])).

tff(c_9845,plain,(
    ! [B_300,B_28] :
      ( r2_hidden('#skF_7','#skF_3'('#skF_5',B_300,k6_waybel_0('#skF_5',B_28)))
      | ~ r1_tarski('#skF_6','#skF_3'('#skF_5',B_300,k6_waybel_0('#skF_5',B_28)))
      | v1_xboole_0('#skF_3'('#skF_5',B_300,k6_waybel_0('#skF_5',B_28)))
      | ~ m1_subset_1(k6_waybel_0('#skF_5',B_28),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_subset_1(B_300,k6_waybel_0('#skF_5',B_28))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_28),'#skF_5')
      | ~ v2_waybel_0(k6_waybel_0('#skF_5',B_28),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_28))
      | ~ m1_subset_1(B_300,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v12_waybel_0(B_300,'#skF_5')
      | ~ v1_waybel_0(B_300,'#skF_5')
      | v1_xboole_0(B_300)
      | ~ v2_lattice3('#skF_5')
      | ~ v1_lattice3('#skF_5')
      | ~ v2_waybel_1('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | ~ m1_subset_1(B_28,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1050,c_9842])).

tff(c_9848,plain,(
    ! [B_300,B_28] :
      ( r2_hidden('#skF_7','#skF_3'('#skF_5',B_300,k6_waybel_0('#skF_5',B_28)))
      | ~ r1_tarski('#skF_6','#skF_3'('#skF_5',B_300,k6_waybel_0('#skF_5',B_28)))
      | v1_xboole_0('#skF_3'('#skF_5',B_300,k6_waybel_0('#skF_5',B_28)))
      | ~ m1_subset_1(k6_waybel_0('#skF_5',B_28),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_subset_1(B_300,k6_waybel_0('#skF_5',B_28))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_28),'#skF_5')
      | ~ v2_waybel_0(k6_waybel_0('#skF_5',B_28),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_28))
      | ~ m1_subset_1(B_300,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v12_waybel_0(B_300,'#skF_5')
      | ~ v1_waybel_0(B_300,'#skF_5')
      | v1_xboole_0(B_300)
      | ~ m1_subset_1(B_28,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_86,c_84,c_82,c_80,c_78,c_76,c_9845])).

tff(c_14640,plain,(
    ! [B_1546,B_1547] :
      ( r2_hidden('#skF_7','#skF_3'('#skF_5',B_1546,k6_waybel_0('#skF_5',B_1547)))
      | ~ r1_tarski('#skF_6','#skF_3'('#skF_5',B_1546,k6_waybel_0('#skF_5',B_1547)))
      | v1_xboole_0('#skF_3'('#skF_5',B_1546,k6_waybel_0('#skF_5',B_1547)))
      | ~ m1_subset_1(k6_waybel_0('#skF_5',B_1547),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_subset_1(B_1546,k6_waybel_0('#skF_5',B_1547))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_1547),'#skF_5')
      | ~ v2_waybel_0(k6_waybel_0('#skF_5',B_1547),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_1547))
      | ~ m1_subset_1(B_1546,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v12_waybel_0(B_1546,'#skF_5')
      | ~ v1_waybel_0(B_1546,'#skF_5')
      | v1_xboole_0(B_1546)
      | ~ m1_subset_1(B_1547,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_9848])).

tff(c_14643,plain,(
    ! [B_1546,B_28] :
      ( r2_hidden('#skF_7','#skF_3'('#skF_5',B_1546,k6_waybel_0('#skF_5',B_28)))
      | ~ r1_tarski('#skF_6','#skF_3'('#skF_5',B_1546,k6_waybel_0('#skF_5',B_28)))
      | v1_xboole_0('#skF_3'('#skF_5',B_1546,k6_waybel_0('#skF_5',B_28)))
      | ~ r1_subset_1(B_1546,k6_waybel_0('#skF_5',B_28))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_28),'#skF_5')
      | ~ v2_waybel_0(k6_waybel_0('#skF_5',B_28),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_28))
      | ~ m1_subset_1(B_1546,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v12_waybel_0(B_1546,'#skF_5')
      | ~ v1_waybel_0(B_1546,'#skF_5')
      | v1_xboole_0(B_1546)
      | ~ m1_subset_1(B_28,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_14640])).

tff(c_14646,plain,(
    ! [B_1546,B_28] :
      ( r2_hidden('#skF_7','#skF_3'('#skF_5',B_1546,k6_waybel_0('#skF_5',B_28)))
      | ~ r1_tarski('#skF_6','#skF_3'('#skF_5',B_1546,k6_waybel_0('#skF_5',B_28)))
      | v1_xboole_0('#skF_3'('#skF_5',B_1546,k6_waybel_0('#skF_5',B_28)))
      | ~ r1_subset_1(B_1546,k6_waybel_0('#skF_5',B_28))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_28),'#skF_5')
      | ~ v2_waybel_0(k6_waybel_0('#skF_5',B_28),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_28))
      | ~ m1_subset_1(B_1546,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v12_waybel_0(B_1546,'#skF_5')
      | ~ v1_waybel_0(B_1546,'#skF_5')
      | v1_xboole_0(B_1546)
      | ~ m1_subset_1(B_28,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_14643])).

tff(c_25378,plain,(
    ! [B_2254,B_2255] :
      ( r2_hidden('#skF_7','#skF_3'('#skF_5',B_2254,k6_waybel_0('#skF_5',B_2255)))
      | ~ r1_tarski('#skF_6','#skF_3'('#skF_5',B_2254,k6_waybel_0('#skF_5',B_2255)))
      | v1_xboole_0('#skF_3'('#skF_5',B_2254,k6_waybel_0('#skF_5',B_2255)))
      | ~ r1_subset_1(B_2254,k6_waybel_0('#skF_5',B_2255))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_2255),'#skF_5')
      | ~ v2_waybel_0(k6_waybel_0('#skF_5',B_2255),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_2255))
      | ~ m1_subset_1(B_2254,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v12_waybel_0(B_2254,'#skF_5')
      | ~ v1_waybel_0(B_2254,'#skF_5')
      | v1_xboole_0(B_2254)
      | ~ m1_subset_1(B_2255,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_14646])).

tff(c_91,plain,(
    ! [A_90,B_91] :
      ( r1_xboole_0(A_90,B_91)
      | ~ r1_subset_1(A_90,B_91)
      | v1_xboole_0(B_91)
      | v1_xboole_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_52,plain,(
    ! [A_62,B_63,C_66] :
      ( ~ r1_xboole_0(A_62,B_63)
      | ~ r2_hidden(C_66,B_63)
      | ~ r2_hidden(C_66,A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_114,plain,(
    ! [C_99,B_100,A_101] :
      ( ~ r2_hidden(C_99,B_100)
      | ~ r2_hidden(C_99,A_101)
      | ~ r1_subset_1(A_101,B_100)
      | v1_xboole_0(B_100)
      | v1_xboole_0(A_101) ) ),
    inference(resolution,[status(thm)],[c_91,c_52])).

tff(c_175,plain,(
    ! [A_122,B_123,A_124] :
      ( ~ r2_hidden('#skF_4'(A_122,B_123),A_124)
      | ~ r1_subset_1(A_124,A_122)
      | v1_xboole_0(A_122)
      | v1_xboole_0(A_124)
      | r1_xboole_0(A_122,B_123) ) ),
    inference(resolution,[status(thm)],[c_56,c_114])).

tff(c_195,plain,(
    ! [B_127,A_128] :
      ( ~ r1_subset_1(B_127,A_128)
      | v1_xboole_0(A_128)
      | v1_xboole_0(B_127)
      | r1_xboole_0(A_128,B_127) ) ),
    inference(resolution,[status(thm)],[c_54,c_175])).

tff(c_202,plain,(
    ! [C_66,B_127,A_128] :
      ( ~ r2_hidden(C_66,B_127)
      | ~ r2_hidden(C_66,A_128)
      | ~ r1_subset_1(B_127,A_128)
      | v1_xboole_0(A_128)
      | v1_xboole_0(B_127) ) ),
    inference(resolution,[status(thm)],[c_195,c_52])).

tff(c_31056,plain,(
    ! [A_2585,B_2586,B_2587] :
      ( ~ r2_hidden('#skF_7',A_2585)
      | ~ r1_subset_1('#skF_3'('#skF_5',B_2586,k6_waybel_0('#skF_5',B_2587)),A_2585)
      | v1_xboole_0(A_2585)
      | ~ r1_tarski('#skF_6','#skF_3'('#skF_5',B_2586,k6_waybel_0('#skF_5',B_2587)))
      | v1_xboole_0('#skF_3'('#skF_5',B_2586,k6_waybel_0('#skF_5',B_2587)))
      | ~ r1_subset_1(B_2586,k6_waybel_0('#skF_5',B_2587))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_2587),'#skF_5')
      | ~ v2_waybel_0(k6_waybel_0('#skF_5',B_2587),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_2587))
      | ~ m1_subset_1(B_2586,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v12_waybel_0(B_2586,'#skF_5')
      | ~ v1_waybel_0(B_2586,'#skF_5')
      | v1_xboole_0(B_2586)
      | ~ m1_subset_1(B_2587,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_25378,c_202])).

tff(c_31089,plain,(
    ! [B_28,B_258] :
      ( ~ r2_hidden('#skF_7',k6_waybel_0('#skF_5',B_28))
      | ~ r1_tarski('#skF_6','#skF_3'('#skF_5',B_258,k6_waybel_0('#skF_5',B_28)))
      | v1_xboole_0('#skF_3'('#skF_5',B_258,k6_waybel_0('#skF_5',B_28)))
      | ~ r1_subset_1(B_258,k6_waybel_0('#skF_5',B_28))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_28),'#skF_5')
      | ~ v2_waybel_0(k6_waybel_0('#skF_5',B_28),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_28))
      | ~ m1_subset_1(B_258,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v12_waybel_0(B_258,'#skF_5')
      | ~ v1_waybel_0(B_258,'#skF_5')
      | v1_xboole_0(B_258)
      | ~ v2_lattice3('#skF_5')
      | ~ v1_lattice3('#skF_5')
      | ~ v2_waybel_1('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | ~ m1_subset_1(B_28,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_903,c_31056])).

tff(c_31102,plain,(
    ! [B_28,B_258] :
      ( ~ r2_hidden('#skF_7',k6_waybel_0('#skF_5',B_28))
      | ~ r1_tarski('#skF_6','#skF_3'('#skF_5',B_258,k6_waybel_0('#skF_5',B_28)))
      | v1_xboole_0('#skF_3'('#skF_5',B_258,k6_waybel_0('#skF_5',B_28)))
      | ~ r1_subset_1(B_258,k6_waybel_0('#skF_5',B_28))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_28),'#skF_5')
      | ~ v2_waybel_0(k6_waybel_0('#skF_5',B_28),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_28))
      | ~ m1_subset_1(B_258,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v12_waybel_0(B_258,'#skF_5')
      | ~ v1_waybel_0(B_258,'#skF_5')
      | v1_xboole_0(B_258)
      | ~ m1_subset_1(B_28,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_86,c_84,c_82,c_80,c_78,c_76,c_31089])).

tff(c_31104,plain,(
    ! [B_2588,B_2589] :
      ( ~ r2_hidden('#skF_7',k6_waybel_0('#skF_5',B_2588))
      | ~ r1_tarski('#skF_6','#skF_3'('#skF_5',B_2589,k6_waybel_0('#skF_5',B_2588)))
      | v1_xboole_0('#skF_3'('#skF_5',B_2589,k6_waybel_0('#skF_5',B_2588)))
      | ~ r1_subset_1(B_2589,k6_waybel_0('#skF_5',B_2588))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_2588),'#skF_5')
      | ~ v2_waybel_0(k6_waybel_0('#skF_5',B_2588),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_2588))
      | ~ m1_subset_1(B_2589,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v12_waybel_0(B_2589,'#skF_5')
      | ~ v1_waybel_0(B_2589,'#skF_5')
      | v1_xboole_0(B_2589)
      | ~ m1_subset_1(B_2588,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_31102])).

tff(c_31108,plain,(
    ! [B_28] :
      ( ~ r2_hidden('#skF_7',k6_waybel_0('#skF_5',B_28))
      | v1_xboole_0('#skF_3'('#skF_5','#skF_6',k6_waybel_0('#skF_5',B_28)))
      | ~ r1_subset_1('#skF_6',k6_waybel_0('#skF_5',B_28))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_28),'#skF_5')
      | ~ v2_waybel_0(k6_waybel_0('#skF_5',B_28),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_28))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v12_waybel_0('#skF_6','#skF_5')
      | ~ v1_waybel_0('#skF_6','#skF_5')
      | v1_xboole_0('#skF_6')
      | ~ v2_lattice3('#skF_5')
      | ~ v1_lattice3('#skF_5')
      | ~ v2_waybel_1('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | ~ m1_subset_1(B_28,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_859,c_31104])).

tff(c_31111,plain,(
    ! [B_28] :
      ( ~ r2_hidden('#skF_7',k6_waybel_0('#skF_5',B_28))
      | v1_xboole_0('#skF_3'('#skF_5','#skF_6',k6_waybel_0('#skF_5',B_28)))
      | ~ r1_subset_1('#skF_6',k6_waybel_0('#skF_5',B_28))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_28),'#skF_5')
      | ~ v2_waybel_0(k6_waybel_0('#skF_5',B_28),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_28))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(B_28,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_86,c_84,c_82,c_80,c_78,c_76,c_70,c_68,c_66,c_31108])).

tff(c_31113,plain,(
    ! [B_2590] :
      ( ~ r2_hidden('#skF_7',k6_waybel_0('#skF_5',B_2590))
      | v1_xboole_0('#skF_3'('#skF_5','#skF_6',k6_waybel_0('#skF_5',B_2590)))
      | ~ r1_subset_1('#skF_6',k6_waybel_0('#skF_5',B_2590))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_2590),'#skF_5')
      | ~ v2_waybel_0(k6_waybel_0('#skF_5',B_2590),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_2590))
      | ~ m1_subset_1(B_2590,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_72,c_31111])).

tff(c_50,plain,(
    ! [A_48,B_56,C_60] :
      ( ~ v1_xboole_0('#skF_3'(A_48,B_56,C_60))
      | ~ r1_subset_1(B_56,C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ v13_waybel_0(C_60,A_48)
      | ~ v2_waybel_0(C_60,A_48)
      | v1_xboole_0(C_60)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ v12_waybel_0(B_56,A_48)
      | ~ v1_waybel_0(B_56,A_48)
      | v1_xboole_0(B_56)
      | ~ l1_orders_2(A_48)
      | ~ v2_lattice3(A_48)
      | ~ v1_lattice3(A_48)
      | ~ v2_waybel_1(A_48)
      | ~ v5_orders_2(A_48)
      | ~ v4_orders_2(A_48)
      | ~ v3_orders_2(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_31115,plain,(
    ! [B_2590] :
      ( ~ m1_subset_1(k6_waybel_0('#skF_5',B_2590),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v12_waybel_0('#skF_6','#skF_5')
      | ~ v1_waybel_0('#skF_6','#skF_5')
      | v1_xboole_0('#skF_6')
      | ~ l1_orders_2('#skF_5')
      | ~ v2_lattice3('#skF_5')
      | ~ v1_lattice3('#skF_5')
      | ~ v2_waybel_1('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | ~ r2_hidden('#skF_7',k6_waybel_0('#skF_5',B_2590))
      | ~ r1_subset_1('#skF_6',k6_waybel_0('#skF_5',B_2590))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_2590),'#skF_5')
      | ~ v2_waybel_0(k6_waybel_0('#skF_5',B_2590),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_2590))
      | ~ m1_subset_1(B_2590,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_31113,c_50])).

tff(c_31118,plain,(
    ! [B_2590] :
      ( ~ m1_subset_1(k6_waybel_0('#skF_5',B_2590),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v1_xboole_0('#skF_6')
      | ~ r2_hidden('#skF_7',k6_waybel_0('#skF_5',B_2590))
      | ~ r1_subset_1('#skF_6',k6_waybel_0('#skF_5',B_2590))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_2590),'#skF_5')
      | ~ v2_waybel_0(k6_waybel_0('#skF_5',B_2590),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_2590))
      | ~ m1_subset_1(B_2590,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_80,c_78,c_76,c_74,c_70,c_68,c_66,c_31115])).

tff(c_31120,plain,(
    ! [B_2591] :
      ( ~ m1_subset_1(k6_waybel_0('#skF_5',B_2591),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_hidden('#skF_7',k6_waybel_0('#skF_5',B_2591))
      | ~ r1_subset_1('#skF_6',k6_waybel_0('#skF_5',B_2591))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_2591),'#skF_5')
      | ~ v2_waybel_0(k6_waybel_0('#skF_5',B_2591),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_2591))
      | ~ m1_subset_1(B_2591,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_31118])).

tff(c_31124,plain,(
    ! [B_28] :
      ( ~ r2_hidden('#skF_7',k6_waybel_0('#skF_5',B_28))
      | ~ r1_subset_1('#skF_6',k6_waybel_0('#skF_5',B_28))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_28),'#skF_5')
      | ~ v2_waybel_0(k6_waybel_0('#skF_5',B_28),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_28))
      | ~ m1_subset_1(B_28,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_31120])).

tff(c_31127,plain,(
    ! [B_28] :
      ( ~ r2_hidden('#skF_7',k6_waybel_0('#skF_5',B_28))
      | ~ r1_subset_1('#skF_6',k6_waybel_0('#skF_5',B_28))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_28),'#skF_5')
      | ~ v2_waybel_0(k6_waybel_0('#skF_5',B_28),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_28))
      | ~ m1_subset_1(B_28,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_31124])).

tff(c_31129,plain,(
    ! [B_2592] :
      ( ~ r2_hidden('#skF_7',k6_waybel_0('#skF_5',B_2592))
      | ~ r1_subset_1('#skF_6',k6_waybel_0('#skF_5',B_2592))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_2592),'#skF_5')
      | ~ v2_waybel_0(k6_waybel_0('#skF_5',B_2592),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_2592))
      | ~ m1_subset_1(B_2592,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_31127])).

tff(c_31133,plain,(
    ! [B_32] :
      ( ~ r2_hidden('#skF_7',k6_waybel_0('#skF_5',B_32))
      | ~ r1_subset_1('#skF_6',k6_waybel_0('#skF_5',B_32))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_32),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_32))
      | ~ m1_subset_1(B_32,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_20,c_31129])).

tff(c_31136,plain,(
    ! [B_32] :
      ( ~ r2_hidden('#skF_7',k6_waybel_0('#skF_5',B_32))
      | ~ r1_subset_1('#skF_6',k6_waybel_0('#skF_5',B_32))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_32),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_32))
      | ~ m1_subset_1(B_32,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_74,c_31133])).

tff(c_31138,plain,(
    ! [B_2593] :
      ( ~ r2_hidden('#skF_7',k6_waybel_0('#skF_5',B_2593))
      | ~ r1_subset_1('#skF_6',k6_waybel_0('#skF_5',B_2593))
      | ~ v13_waybel_0(k6_waybel_0('#skF_5',B_2593),'#skF_5')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_2593))
      | ~ m1_subset_1(B_2593,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_31136])).

tff(c_31142,plain,(
    ! [B_30] :
      ( ~ r2_hidden('#skF_7',k6_waybel_0('#skF_5',B_30))
      | ~ r1_subset_1('#skF_6',k6_waybel_0('#skF_5',B_30))
      | v1_xboole_0(k6_waybel_0('#skF_5',B_30))
      | ~ m1_subset_1(B_30,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_18,c_31138])).

tff(c_31145,plain,(
    ! [B_30] :
      ( ~ r2_hidden('#skF_7',k6_waybel_0('#skF_5',B_30))
      | ~ r1_subset_1('#skF_6',k6_waybel_0('#skF_5',B_30))
      | v1_xboole_0(k6_waybel_0('#skF_5',B_30))
      | ~ m1_subset_1(B_30,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_74,c_31142])).

tff(c_31147,plain,(
    ! [B_2594] :
      ( ~ r2_hidden('#skF_7',k6_waybel_0('#skF_5',B_2594))
      | ~ r1_subset_1('#skF_6',k6_waybel_0('#skF_5',B_2594))
      | v1_xboole_0(k6_waybel_0('#skF_5',B_2594))
      | ~ m1_subset_1(B_2594,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_31145])).

tff(c_31151,plain,(
    ! [B_45] :
      ( ~ r1_subset_1('#skF_6',k6_waybel_0('#skF_5',B_45))
      | v1_xboole_0(k6_waybel_0('#skF_5',B_45))
      | ~ r1_orders_2('#skF_5',B_45,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_45,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_31147])).

tff(c_31154,plain,(
    ! [B_45] :
      ( ~ r1_subset_1('#skF_6',k6_waybel_0('#skF_5',B_45))
      | v1_xboole_0(k6_waybel_0('#skF_5',B_45))
      | ~ r1_orders_2('#skF_5',B_45,'#skF_7')
      | ~ m1_subset_1(B_45,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_64,c_31151])).

tff(c_31156,plain,(
    ! [B_2595] :
      ( ~ r1_subset_1('#skF_6',k6_waybel_0('#skF_5',B_2595))
      | v1_xboole_0(k6_waybel_0('#skF_5',B_2595))
      | ~ r1_orders_2('#skF_5',B_2595,'#skF_7')
      | ~ m1_subset_1(B_2595,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_31154])).

tff(c_31241,plain,(
    ! [B_2596] :
      ( ~ r1_orders_2('#skF_5',B_2596,'#skF_7')
      | v1_xboole_0(k6_waybel_0('#skF_5',B_2596))
      | r2_hidden(B_2596,'#skF_6')
      | ~ m1_subset_1(B_2596,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1684,c_31156])).

tff(c_31275,plain,
    ( ~ r1_orders_2('#skF_5','#skF_7','#skF_7')
    | v1_xboole_0(k6_waybel_0('#skF_5','#skF_7'))
    | r2_hidden('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_31241])).

tff(c_31303,plain,
    ( v1_xboole_0(k6_waybel_0('#skF_5','#skF_7'))
    | r2_hidden('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_555,c_31275])).

tff(c_31305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_134,c_31303])).

tff(c_31306,plain,(
    v2_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_31310,plain,
    ( ~ v2_lattice3('#skF_5')
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_31306,c_2])).

tff(c_31314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_31310])).

%------------------------------------------------------------------------------
