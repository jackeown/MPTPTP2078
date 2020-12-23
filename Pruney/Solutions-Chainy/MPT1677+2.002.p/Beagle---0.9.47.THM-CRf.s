%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:02 EST 2020

% Result     : Theorem 4.76s
% Output     : CNFRefutation 4.76s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 218 expanded)
%              Number of leaves         :   41 (  94 expanded)
%              Depth                    :   26
%              Number of atoms          :  331 (1335 expanded)
%              Number of equality atoms :   22 ( 137 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r2_hidden > r1_tarski > m1_subset_1 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_finset_1 > l1_orders_2 > k2_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

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

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

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

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_196,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( ! [D] :
                        ( ( v1_finset_1(D)
                          & m1_subset_1(D,k1_zfmisc_1(B)) )
                       => ( D != k1_xboole_0
                         => r2_yellow_0(A,D) ) )
                    & ! [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                       => ~ ( r2_hidden(D,C)
                            & ! [E] :
                                ( ( v1_finset_1(E)
                                  & m1_subset_1(E,k1_zfmisc_1(B)) )
                               => ~ ( r2_yellow_0(A,E)
                                    & D = k2_yellow_0(A,E) ) ) ) )
                    & ! [D] :
                        ( ( v1_finset_1(D)
                          & m1_subset_1(D,k1_zfmisc_1(B)) )
                       => ( D != k1_xboole_0
                         => r2_hidden(k2_yellow_0(A,D),C) ) ) )
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r1_lattice3(A,B,D)
                      <=> r1_lattice3(A,C,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_waybel_0)).

tff(f_59,axiom,(
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

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_45,axiom,(
    ! [A] : v1_finset_1(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_77,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_137,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => ! [D] :
              ( m1_subset_1(D,u1_struct_0(A))
             => ( ( r1_lattice3(A,C,D)
                 => r1_lattice3(A,B,D) )
                & ( r2_lattice3(A,C,D)
                 => r2_lattice3(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).

tff(f_121,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( r1_lattice3(A,k1_tarski(C),B)
                 => r1_orders_2(A,B,C) )
                & ( r1_orders_2(A,B,C)
                 => r1_lattice3(A,k1_tarski(C),B) )
                & ( r2_lattice3(A,k1_tarski(C),B)
                 => r1_orders_2(A,C,B) )
                & ( r1_orders_2(A,C,B)
                 => r2_lattice3(A,k1_tarski(C),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).

tff(f_97,axiom,(
    ! [A] :
      ( ( v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ! [D] :
              ( m1_subset_1(D,u1_struct_0(A))
             => ( ( r1_lattice3(A,B,C)
                  & r1_orders_2(A,D,C) )
               => r1_lattice3(A,B,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow_0)).

tff(f_29,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k2_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_74,plain,
    ( r1_lattice3('#skF_3','#skF_4','#skF_7')
    | r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_99,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_68,plain,
    ( ~ r1_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_108,plain,(
    ~ r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_68])).

tff(c_60,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_20,plain,(
    ! [A_10,B_17,C_18] :
      ( r2_hidden('#skF_1'(A_10,B_17,C_18),B_17)
      | r1_lattice3(A_10,B_17,C_18)
      | ~ m1_subset_1(C_18,u1_struct_0(A_10))
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_122,plain,(
    ! [A_124,C_125,B_126] :
      ( m1_subset_1(A_124,C_125)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(C_125))
      | ~ r2_hidden(A_124,B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_133,plain,(
    ! [A_124] :
      ( m1_subset_1(A_124,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_124,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_122])).

tff(c_14,plain,(
    ! [A_9] : v1_finset_1(k1_tarski(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(k1_tarski(A_2),k1_zfmisc_1(B_3))
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_148,plain,(
    ! [D_134] :
      ( r2_yellow_0('#skF_3',D_134)
      | k1_xboole_0 = D_134
      | ~ m1_subset_1(D_134,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_152,plain,(
    ! [A_2] :
      ( r2_yellow_0('#skF_3',k1_tarski(A_2))
      | k1_tarski(A_2) = k1_xboole_0
      | ~ v1_finset_1(k1_tarski(A_2))
      | ~ r2_hidden(A_2,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6,c_148])).

tff(c_159,plain,(
    ! [A_2] :
      ( r2_yellow_0('#skF_3',k1_tarski(A_2))
      | k1_tarski(A_2) = k1_xboole_0
      | ~ r2_hidden(A_2,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_152])).

tff(c_52,plain,(
    ! [D_110] :
      ( r2_hidden(k2_yellow_0('#skF_3',D_110),'#skF_5')
      | k1_xboole_0 = D_110
      | ~ m1_subset_1(D_110,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_134,plain,(
    ! [A_124] :
      ( m1_subset_1(A_124,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_124,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_122])).

tff(c_251,plain,(
    ! [A_155,B_156] :
      ( r1_lattice3(A_155,B_156,k2_yellow_0(A_155,B_156))
      | ~ r2_yellow_0(A_155,B_156)
      | ~ m1_subset_1(k2_yellow_0(A_155,B_156),u1_struct_0(A_155))
      | ~ l1_orders_2(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_259,plain,(
    ! [B_156] :
      ( r1_lattice3('#skF_3',B_156,k2_yellow_0('#skF_3',B_156))
      | ~ r2_yellow_0('#skF_3',B_156)
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden(k2_yellow_0('#skF_3',B_156),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_134,c_251])).

tff(c_272,plain,(
    ! [B_156] :
      ( r1_lattice3('#skF_3',B_156,k2_yellow_0('#skF_3',B_156))
      | ~ r2_yellow_0('#skF_3',B_156)
      | ~ r2_hidden(k2_yellow_0('#skF_3',B_156),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_259])).

tff(c_62,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_101,plain,(
    ! [A_119,B_120] :
      ( m1_subset_1(k1_tarski(A_119),k1_zfmisc_1(B_120))
      | ~ r2_hidden(A_119,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_105,plain,(
    ! [A_119,B_120] :
      ( r1_tarski(k1_tarski(A_119),B_120)
      | ~ r2_hidden(A_119,B_120) ) ),
    inference(resolution,[status(thm)],[c_101,c_8])).

tff(c_295,plain,(
    ! [A_169,B_170,D_171,C_172] :
      ( r1_lattice3(A_169,B_170,D_171)
      | ~ r1_lattice3(A_169,C_172,D_171)
      | ~ m1_subset_1(D_171,u1_struct_0(A_169))
      | ~ r1_tarski(B_170,C_172)
      | ~ l1_orders_2(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_305,plain,(
    ! [B_170] :
      ( r1_lattice3('#skF_3',B_170,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_170,'#skF_5')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_99,c_295])).

tff(c_318,plain,(
    ! [B_170] :
      ( r1_lattice3('#skF_3',B_170,'#skF_7')
      | ~ r1_tarski(B_170,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_305])).

tff(c_369,plain,(
    ! [A_181,B_182,C_183] :
      ( r1_orders_2(A_181,B_182,C_183)
      | ~ r1_lattice3(A_181,k1_tarski(C_183),B_182)
      | ~ m1_subset_1(C_183,u1_struct_0(A_181))
      | ~ m1_subset_1(B_182,u1_struct_0(A_181))
      | ~ l1_orders_2(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_377,plain,(
    ! [C_183] :
      ( r1_orders_2('#skF_3','#skF_7',C_183)
      | ~ m1_subset_1(C_183,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r1_tarski(k1_tarski(C_183),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_318,c_369])).

tff(c_403,plain,(
    ! [C_184] :
      ( r1_orders_2('#skF_3','#skF_7',C_184)
      | ~ m1_subset_1(C_184,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(C_184),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_377])).

tff(c_409,plain,(
    ! [A_185] :
      ( r1_orders_2('#skF_3','#skF_7',A_185)
      | ~ m1_subset_1(A_185,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_185,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_105,c_403])).

tff(c_437,plain,(
    ! [A_124] :
      ( r1_orders_2('#skF_3','#skF_7',A_124)
      | ~ r2_hidden(A_124,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_134,c_409])).

tff(c_871,plain,(
    ! [A_291,B_292,D_293,C_294] :
      ( r1_lattice3(A_291,B_292,D_293)
      | ~ r1_orders_2(A_291,D_293,C_294)
      | ~ r1_lattice3(A_291,B_292,C_294)
      | ~ m1_subset_1(D_293,u1_struct_0(A_291))
      | ~ m1_subset_1(C_294,u1_struct_0(A_291))
      | ~ l1_orders_2(A_291)
      | ~ v4_orders_2(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_875,plain,(
    ! [B_292,A_124] :
      ( r1_lattice3('#skF_3',B_292,'#skF_7')
      | ~ r1_lattice3('#skF_3',B_292,A_124)
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_124,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ r2_hidden(A_124,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_437,c_871])).

tff(c_882,plain,(
    ! [B_295,A_296] :
      ( r1_lattice3('#skF_3',B_295,'#skF_7')
      | ~ r1_lattice3('#skF_3',B_295,A_296)
      | ~ m1_subset_1(A_296,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_296,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_50,c_875])).

tff(c_963,plain,(
    ! [B_298] :
      ( r1_lattice3('#skF_3',B_298,'#skF_7')
      | ~ m1_subset_1(k2_yellow_0('#skF_3',B_298),u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3',B_298)
      | ~ r2_hidden(k2_yellow_0('#skF_3',B_298),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_272,c_882])).

tff(c_990,plain,(
    ! [B_299] :
      ( r1_lattice3('#skF_3',B_299,'#skF_7')
      | ~ r2_yellow_0('#skF_3',B_299)
      | ~ r2_hidden(k2_yellow_0('#skF_3',B_299),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_134,c_963])).

tff(c_998,plain,(
    ! [D_300] :
      ( r1_lattice3('#skF_3',D_300,'#skF_7')
      | ~ r2_yellow_0('#skF_3',D_300)
      | k1_xboole_0 = D_300
      | ~ m1_subset_1(D_300,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_300) ) ),
    inference(resolution,[status(thm)],[c_52,c_990])).

tff(c_1017,plain,(
    ! [A_2] :
      ( r1_lattice3('#skF_3',k1_tarski(A_2),'#skF_7')
      | ~ r2_yellow_0('#skF_3',k1_tarski(A_2))
      | k1_tarski(A_2) = k1_xboole_0
      | ~ v1_finset_1(k1_tarski(A_2))
      | ~ r2_hidden(A_2,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6,c_998])).

tff(c_1090,plain,(
    ! [A_306] :
      ( r1_lattice3('#skF_3',k1_tarski(A_306),'#skF_7')
      | ~ r2_yellow_0('#skF_3',k1_tarski(A_306))
      | k1_tarski(A_306) = k1_xboole_0
      | ~ r2_hidden(A_306,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1017])).

tff(c_44,plain,(
    ! [A_45,B_49,C_51] :
      ( r1_orders_2(A_45,B_49,C_51)
      | ~ r1_lattice3(A_45,k1_tarski(C_51),B_49)
      | ~ m1_subset_1(C_51,u1_struct_0(A_45))
      | ~ m1_subset_1(B_49,u1_struct_0(A_45))
      | ~ l1_orders_2(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1095,plain,(
    ! [A_306] :
      ( r1_orders_2('#skF_3','#skF_7',A_306)
      | ~ m1_subset_1(A_306,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_yellow_0('#skF_3',k1_tarski(A_306))
      | k1_tarski(A_306) = k1_xboole_0
      | ~ r2_hidden(A_306,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1090,c_44])).

tff(c_1185,plain,(
    ! [A_320] :
      ( r1_orders_2('#skF_3','#skF_7',A_320)
      | ~ m1_subset_1(A_320,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3',k1_tarski(A_320))
      | k1_tarski(A_320) = k1_xboole_0
      | ~ r2_hidden(A_320,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_1095])).

tff(c_1196,plain,(
    ! [A_321] :
      ( r1_orders_2('#skF_3','#skF_7',A_321)
      | ~ m1_subset_1(A_321,u1_struct_0('#skF_3'))
      | k1_tarski(A_321) = k1_xboole_0
      | ~ r2_hidden(A_321,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_159,c_1185])).

tff(c_1247,plain,(
    ! [A_322] :
      ( r1_orders_2('#skF_3','#skF_7',A_322)
      | k1_tarski(A_322) = k1_xboole_0
      | ~ r2_hidden(A_322,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_133,c_1196])).

tff(c_18,plain,(
    ! [A_10,C_18,B_17] :
      ( ~ r1_orders_2(A_10,C_18,'#skF_1'(A_10,B_17,C_18))
      | r1_lattice3(A_10,B_17,C_18)
      | ~ m1_subset_1(C_18,u1_struct_0(A_10))
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1255,plain,(
    ! [B_17] :
      ( r1_lattice3('#skF_3',B_17,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | k1_tarski('#skF_1'('#skF_3',B_17,'#skF_7')) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_17,'#skF_7'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1247,c_18])).

tff(c_1281,plain,(
    ! [B_327] :
      ( r1_lattice3('#skF_3',B_327,'#skF_7')
      | k1_tarski('#skF_1'('#skF_3',B_327,'#skF_7')) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_327,'#skF_7'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_1255])).

tff(c_1285,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r1_lattice3('#skF_3','#skF_4','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1281])).

tff(c_1288,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_1285])).

tff(c_1289,plain,(
    k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_1288])).

tff(c_4,plain,(
    ! [A_1] : ~ v1_xboole_0(k1_tarski(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1345,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1289,c_4])).

tff(c_1360,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1345])).

tff(c_1361,plain,(
    r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_1364,plain,(
    ~ r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1361,c_68])).

tff(c_1372,plain,(
    ! [A_334,C_335,B_336] :
      ( m1_subset_1(A_334,C_335)
      | ~ m1_subset_1(B_336,k1_zfmisc_1(C_335))
      | ~ r2_hidden(A_334,B_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1384,plain,(
    ! [A_334] :
      ( m1_subset_1(A_334,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_334,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_1372])).

tff(c_1461,plain,(
    ! [D_353] :
      ( m1_subset_1('#skF_6'(D_353),k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(D_353,'#skF_5')
      | ~ m1_subset_1(D_353,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_1472,plain,(
    ! [D_353] :
      ( r1_tarski('#skF_6'(D_353),'#skF_4')
      | ~ r2_hidden(D_353,'#skF_5')
      | ~ m1_subset_1(D_353,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1461,c_8])).

tff(c_78,plain,(
    ! [D_108] :
      ( r2_yellow_0('#skF_3','#skF_6'(D_108))
      | ~ r2_hidden(D_108,'#skF_5')
      | ~ m1_subset_1(D_108,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_1516,plain,(
    ! [A_369,B_370,D_371,C_372] :
      ( r1_lattice3(A_369,B_370,D_371)
      | ~ r1_lattice3(A_369,C_372,D_371)
      | ~ m1_subset_1(D_371,u1_struct_0(A_369))
      | ~ r1_tarski(B_370,C_372)
      | ~ l1_orders_2(A_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1518,plain,(
    ! [B_370] :
      ( r1_lattice3('#skF_3',B_370,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_370,'#skF_4')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1361,c_1516])).

tff(c_1521,plain,(
    ! [B_370] :
      ( r1_lattice3('#skF_3',B_370,'#skF_7')
      | ~ r1_tarski(B_370,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_1518])).

tff(c_1427,plain,(
    ! [D_351] :
      ( k2_yellow_0('#skF_3','#skF_6'(D_351)) = D_351
      | ~ r2_hidden(D_351,'#skF_5')
      | ~ m1_subset_1(D_351,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_1441,plain,(
    ! [A_334] :
      ( k2_yellow_0('#skF_3','#skF_6'(A_334)) = A_334
      | ~ r2_hidden(A_334,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1384,c_1427])).

tff(c_34,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(k2_yellow_0(A_34,B_35),u1_struct_0(A_34))
      | ~ l1_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2181,plain,(
    ! [A_497,D_498,B_499] :
      ( r1_orders_2(A_497,D_498,k2_yellow_0(A_497,B_499))
      | ~ r1_lattice3(A_497,B_499,D_498)
      | ~ m1_subset_1(D_498,u1_struct_0(A_497))
      | ~ r2_yellow_0(A_497,B_499)
      | ~ m1_subset_1(k2_yellow_0(A_497,B_499),u1_struct_0(A_497))
      | ~ l1_orders_2(A_497) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2207,plain,(
    ! [A_500,D_501,B_502] :
      ( r1_orders_2(A_500,D_501,k2_yellow_0(A_500,B_502))
      | ~ r1_lattice3(A_500,B_502,D_501)
      | ~ m1_subset_1(D_501,u1_struct_0(A_500))
      | ~ r2_yellow_0(A_500,B_502)
      | ~ l1_orders_2(A_500) ) ),
    inference(resolution,[status(thm)],[c_34,c_2181])).

tff(c_2219,plain,(
    ! [D_501,A_334] :
      ( r1_orders_2('#skF_3',D_501,A_334)
      | ~ r1_lattice3('#skF_3','#skF_6'(A_334),D_501)
      | ~ m1_subset_1(D_501,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3','#skF_6'(A_334))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden(A_334,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1441,c_2207])).

tff(c_2227,plain,(
    ! [D_503,A_504] :
      ( r1_orders_2('#skF_3',D_503,A_504)
      | ~ r1_lattice3('#skF_3','#skF_6'(A_504),D_503)
      | ~ m1_subset_1(D_503,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3','#skF_6'(A_504))
      | ~ r2_hidden(A_504,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2219])).

tff(c_2276,plain,(
    ! [A_504] :
      ( r1_orders_2('#skF_3','#skF_7',A_504)
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3','#skF_6'(A_504))
      | ~ r2_hidden(A_504,'#skF_5')
      | ~ r1_tarski('#skF_6'(A_504),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1521,c_2227])).

tff(c_2359,plain,(
    ! [A_508] :
      ( r1_orders_2('#skF_3','#skF_7',A_508)
      | ~ r2_yellow_0('#skF_3','#skF_6'(A_508))
      | ~ r2_hidden(A_508,'#skF_5')
      | ~ r1_tarski('#skF_6'(A_508),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2276])).

tff(c_2368,plain,(
    ! [D_509] :
      ( r1_orders_2('#skF_3','#skF_7',D_509)
      | ~ r1_tarski('#skF_6'(D_509),'#skF_4')
      | ~ r2_hidden(D_509,'#skF_5')
      | ~ m1_subset_1(D_509,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_78,c_2359])).

tff(c_2386,plain,(
    ! [D_514] :
      ( r1_orders_2('#skF_3','#skF_7',D_514)
      | ~ r2_hidden(D_514,'#skF_5')
      | ~ m1_subset_1(D_514,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1472,c_2368])).

tff(c_2437,plain,(
    ! [A_515] :
      ( r1_orders_2('#skF_3','#skF_7',A_515)
      | ~ r2_hidden(A_515,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1384,c_2386])).

tff(c_2445,plain,(
    ! [B_17] :
      ( r1_lattice3('#skF_3',B_17,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_17,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2437,c_18])).

tff(c_2455,plain,(
    ! [B_516] :
      ( r1_lattice3('#skF_3',B_516,'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_3',B_516,'#skF_7'),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_2445])).

tff(c_2459,plain,
    ( r1_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_2455])).

tff(c_2462,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_2459])).

tff(c_2464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1364,c_2462])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.07  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.06/0.25  % Computer   : n017.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % DateTime   : Tue Dec  1 19:07:16 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.10/0.25  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.76/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.75  
% 4.76/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.75  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r2_hidden > r1_tarski > m1_subset_1 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_finset_1 > l1_orders_2 > k2_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_6
% 4.76/1.75  
% 4.76/1.75  %Foreground sorts:
% 4.76/1.75  
% 4.76/1.75  
% 4.76/1.75  %Background operators:
% 4.76/1.75  
% 4.76/1.75  
% 4.76/1.75  %Foreground operators:
% 4.76/1.75  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.76/1.75  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.76/1.75  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.76/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.76/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.76/1.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.76/1.75  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.76/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.76/1.75  tff('#skF_7', type, '#skF_7': $i).
% 4.76/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.76/1.75  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 4.76/1.75  tff('#skF_5', type, '#skF_5': $i).
% 4.76/1.75  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 4.76/1.75  tff('#skF_3', type, '#skF_3': $i).
% 4.76/1.75  tff(k2_yellow_0, type, k2_yellow_0: ($i * $i) > $i).
% 4.76/1.75  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.76/1.75  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 4.76/1.75  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.76/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.76/1.75  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.76/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.76/1.75  tff('#skF_4', type, '#skF_4': $i).
% 4.76/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.76/1.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.76/1.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.76/1.75  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 4.76/1.75  tff('#skF_6', type, '#skF_6': $i > $i).
% 4.76/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.76/1.75  
% 4.76/1.77  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.76/1.77  tff(f_196, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((((![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r2_yellow_0(A, D)))) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => ~(r2_hidden(D, C) & (![E]: ((v1_finset_1(E) & m1_subset_1(E, k1_zfmisc_1(B))) => ~(r2_yellow_0(A, E) & (D = k2_yellow_0(A, E))))))))) & (![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r2_hidden(k2_yellow_0(A, D), C))))) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, B, D) <=> r1_lattice3(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_waybel_0)).
% 4.76/1.77  tff(f_59, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 4.76/1.77  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.76/1.77  tff(f_45, axiom, (![A]: v1_finset_1(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_finset_1)).
% 4.76/1.77  tff(f_33, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 4.76/1.77  tff(f_77, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_yellow_0(A, B) => ((C = k2_yellow_0(A, B)) <=> (r1_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, B, D) => r1_orders_2(A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_yellow_0)).
% 4.76/1.77  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.76/1.77  tff(f_137, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (r1_tarski(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_lattice3(A, C, D) => r1_lattice3(A, B, D)) & (r2_lattice3(A, C, D) => r2_lattice3(A, B, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_yellow_0)).
% 4.76/1.77  tff(f_121, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((((r1_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, B, C)) & (r1_orders_2(A, B, C) => r1_lattice3(A, k1_tarski(C), B))) & (r2_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, C, B))) & (r1_orders_2(A, C, B) => r2_lattice3(A, k1_tarski(C), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_0)).
% 4.76/1.77  tff(f_97, axiom, (![A]: ((v4_orders_2(A) & l1_orders_2(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_lattice3(A, B, C) & r1_orders_2(A, D, C)) => r1_lattice3(A, B, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_yellow_0)).
% 4.76/1.77  tff(f_29, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 4.76/1.77  tff(f_81, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k2_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_0)).
% 4.76/1.77  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.76/1.77  tff(c_74, plain, (r1_lattice3('#skF_3', '#skF_4', '#skF_7') | r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.76/1.77  tff(c_99, plain, (r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_74])).
% 4.76/1.77  tff(c_68, plain, (~r1_lattice3('#skF_3', '#skF_5', '#skF_7') | ~r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.76/1.77  tff(c_108, plain, (~r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_68])).
% 4.76/1.77  tff(c_60, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.76/1.77  tff(c_50, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.76/1.77  tff(c_20, plain, (![A_10, B_17, C_18]: (r2_hidden('#skF_1'(A_10, B_17, C_18), B_17) | r1_lattice3(A_10, B_17, C_18) | ~m1_subset_1(C_18, u1_struct_0(A_10)) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.76/1.77  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.76/1.77  tff(c_122, plain, (![A_124, C_125, B_126]: (m1_subset_1(A_124, C_125) | ~m1_subset_1(B_126, k1_zfmisc_1(C_125)) | ~r2_hidden(A_124, B_126))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.76/1.77  tff(c_133, plain, (![A_124]: (m1_subset_1(A_124, u1_struct_0('#skF_3')) | ~r2_hidden(A_124, '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_122])).
% 4.76/1.77  tff(c_14, plain, (![A_9]: (v1_finset_1(k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.76/1.77  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(k1_tarski(A_2), k1_zfmisc_1(B_3)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.76/1.77  tff(c_148, plain, (![D_134]: (r2_yellow_0('#skF_3', D_134) | k1_xboole_0=D_134 | ~m1_subset_1(D_134, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_134))), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.76/1.77  tff(c_152, plain, (![A_2]: (r2_yellow_0('#skF_3', k1_tarski(A_2)) | k1_tarski(A_2)=k1_xboole_0 | ~v1_finset_1(k1_tarski(A_2)) | ~r2_hidden(A_2, '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_148])).
% 4.76/1.77  tff(c_159, plain, (![A_2]: (r2_yellow_0('#skF_3', k1_tarski(A_2)) | k1_tarski(A_2)=k1_xboole_0 | ~r2_hidden(A_2, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_152])).
% 4.76/1.77  tff(c_52, plain, (![D_110]: (r2_hidden(k2_yellow_0('#skF_3', D_110), '#skF_5') | k1_xboole_0=D_110 | ~m1_subset_1(D_110, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_110))), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.76/1.77  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.76/1.77  tff(c_134, plain, (![A_124]: (m1_subset_1(A_124, u1_struct_0('#skF_3')) | ~r2_hidden(A_124, '#skF_5'))), inference(resolution, [status(thm)], [c_56, c_122])).
% 4.76/1.77  tff(c_251, plain, (![A_155, B_156]: (r1_lattice3(A_155, B_156, k2_yellow_0(A_155, B_156)) | ~r2_yellow_0(A_155, B_156) | ~m1_subset_1(k2_yellow_0(A_155, B_156), u1_struct_0(A_155)) | ~l1_orders_2(A_155))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.76/1.77  tff(c_259, plain, (![B_156]: (r1_lattice3('#skF_3', B_156, k2_yellow_0('#skF_3', B_156)) | ~r2_yellow_0('#skF_3', B_156) | ~l1_orders_2('#skF_3') | ~r2_hidden(k2_yellow_0('#skF_3', B_156), '#skF_5'))), inference(resolution, [status(thm)], [c_134, c_251])).
% 4.76/1.77  tff(c_272, plain, (![B_156]: (r1_lattice3('#skF_3', B_156, k2_yellow_0('#skF_3', B_156)) | ~r2_yellow_0('#skF_3', B_156) | ~r2_hidden(k2_yellow_0('#skF_3', B_156), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_259])).
% 4.76/1.77  tff(c_62, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.76/1.77  tff(c_101, plain, (![A_119, B_120]: (m1_subset_1(k1_tarski(A_119), k1_zfmisc_1(B_120)) | ~r2_hidden(A_119, B_120))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.76/1.77  tff(c_8, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.76/1.77  tff(c_105, plain, (![A_119, B_120]: (r1_tarski(k1_tarski(A_119), B_120) | ~r2_hidden(A_119, B_120))), inference(resolution, [status(thm)], [c_101, c_8])).
% 4.76/1.77  tff(c_295, plain, (![A_169, B_170, D_171, C_172]: (r1_lattice3(A_169, B_170, D_171) | ~r1_lattice3(A_169, C_172, D_171) | ~m1_subset_1(D_171, u1_struct_0(A_169)) | ~r1_tarski(B_170, C_172) | ~l1_orders_2(A_169))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.76/1.77  tff(c_305, plain, (![B_170]: (r1_lattice3('#skF_3', B_170, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_tarski(B_170, '#skF_5') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_99, c_295])).
% 4.76/1.77  tff(c_318, plain, (![B_170]: (r1_lattice3('#skF_3', B_170, '#skF_7') | ~r1_tarski(B_170, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_305])).
% 4.76/1.77  tff(c_369, plain, (![A_181, B_182, C_183]: (r1_orders_2(A_181, B_182, C_183) | ~r1_lattice3(A_181, k1_tarski(C_183), B_182) | ~m1_subset_1(C_183, u1_struct_0(A_181)) | ~m1_subset_1(B_182, u1_struct_0(A_181)) | ~l1_orders_2(A_181))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.76/1.77  tff(c_377, plain, (![C_183]: (r1_orders_2('#skF_3', '#skF_7', C_183) | ~m1_subset_1(C_183, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r1_tarski(k1_tarski(C_183), '#skF_5'))), inference(resolution, [status(thm)], [c_318, c_369])).
% 4.76/1.77  tff(c_403, plain, (![C_184]: (r1_orders_2('#skF_3', '#skF_7', C_184) | ~m1_subset_1(C_184, u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski(C_184), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_377])).
% 4.76/1.77  tff(c_409, plain, (![A_185]: (r1_orders_2('#skF_3', '#skF_7', A_185) | ~m1_subset_1(A_185, u1_struct_0('#skF_3')) | ~r2_hidden(A_185, '#skF_5'))), inference(resolution, [status(thm)], [c_105, c_403])).
% 4.76/1.77  tff(c_437, plain, (![A_124]: (r1_orders_2('#skF_3', '#skF_7', A_124) | ~r2_hidden(A_124, '#skF_5'))), inference(resolution, [status(thm)], [c_134, c_409])).
% 4.76/1.77  tff(c_871, plain, (![A_291, B_292, D_293, C_294]: (r1_lattice3(A_291, B_292, D_293) | ~r1_orders_2(A_291, D_293, C_294) | ~r1_lattice3(A_291, B_292, C_294) | ~m1_subset_1(D_293, u1_struct_0(A_291)) | ~m1_subset_1(C_294, u1_struct_0(A_291)) | ~l1_orders_2(A_291) | ~v4_orders_2(A_291))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.76/1.77  tff(c_875, plain, (![B_292, A_124]: (r1_lattice3('#skF_3', B_292, '#skF_7') | ~r1_lattice3('#skF_3', B_292, A_124) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~m1_subset_1(A_124, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~r2_hidden(A_124, '#skF_5'))), inference(resolution, [status(thm)], [c_437, c_871])).
% 4.76/1.77  tff(c_882, plain, (![B_295, A_296]: (r1_lattice3('#skF_3', B_295, '#skF_7') | ~r1_lattice3('#skF_3', B_295, A_296) | ~m1_subset_1(A_296, u1_struct_0('#skF_3')) | ~r2_hidden(A_296, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_50, c_875])).
% 4.76/1.77  tff(c_963, plain, (![B_298]: (r1_lattice3('#skF_3', B_298, '#skF_7') | ~m1_subset_1(k2_yellow_0('#skF_3', B_298), u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', B_298) | ~r2_hidden(k2_yellow_0('#skF_3', B_298), '#skF_5'))), inference(resolution, [status(thm)], [c_272, c_882])).
% 4.76/1.77  tff(c_990, plain, (![B_299]: (r1_lattice3('#skF_3', B_299, '#skF_7') | ~r2_yellow_0('#skF_3', B_299) | ~r2_hidden(k2_yellow_0('#skF_3', B_299), '#skF_5'))), inference(resolution, [status(thm)], [c_134, c_963])).
% 4.76/1.77  tff(c_998, plain, (![D_300]: (r1_lattice3('#skF_3', D_300, '#skF_7') | ~r2_yellow_0('#skF_3', D_300) | k1_xboole_0=D_300 | ~m1_subset_1(D_300, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_300))), inference(resolution, [status(thm)], [c_52, c_990])).
% 4.76/1.77  tff(c_1017, plain, (![A_2]: (r1_lattice3('#skF_3', k1_tarski(A_2), '#skF_7') | ~r2_yellow_0('#skF_3', k1_tarski(A_2)) | k1_tarski(A_2)=k1_xboole_0 | ~v1_finset_1(k1_tarski(A_2)) | ~r2_hidden(A_2, '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_998])).
% 4.76/1.77  tff(c_1090, plain, (![A_306]: (r1_lattice3('#skF_3', k1_tarski(A_306), '#skF_7') | ~r2_yellow_0('#skF_3', k1_tarski(A_306)) | k1_tarski(A_306)=k1_xboole_0 | ~r2_hidden(A_306, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1017])).
% 4.76/1.77  tff(c_44, plain, (![A_45, B_49, C_51]: (r1_orders_2(A_45, B_49, C_51) | ~r1_lattice3(A_45, k1_tarski(C_51), B_49) | ~m1_subset_1(C_51, u1_struct_0(A_45)) | ~m1_subset_1(B_49, u1_struct_0(A_45)) | ~l1_orders_2(A_45))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.76/1.77  tff(c_1095, plain, (![A_306]: (r1_orders_2('#skF_3', '#skF_7', A_306) | ~m1_subset_1(A_306, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r2_yellow_0('#skF_3', k1_tarski(A_306)) | k1_tarski(A_306)=k1_xboole_0 | ~r2_hidden(A_306, '#skF_4'))), inference(resolution, [status(thm)], [c_1090, c_44])).
% 4.76/1.77  tff(c_1185, plain, (![A_320]: (r1_orders_2('#skF_3', '#skF_7', A_320) | ~m1_subset_1(A_320, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', k1_tarski(A_320)) | k1_tarski(A_320)=k1_xboole_0 | ~r2_hidden(A_320, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_1095])).
% 4.76/1.77  tff(c_1196, plain, (![A_321]: (r1_orders_2('#skF_3', '#skF_7', A_321) | ~m1_subset_1(A_321, u1_struct_0('#skF_3')) | k1_tarski(A_321)=k1_xboole_0 | ~r2_hidden(A_321, '#skF_4'))), inference(resolution, [status(thm)], [c_159, c_1185])).
% 4.76/1.77  tff(c_1247, plain, (![A_322]: (r1_orders_2('#skF_3', '#skF_7', A_322) | k1_tarski(A_322)=k1_xboole_0 | ~r2_hidden(A_322, '#skF_4'))), inference(resolution, [status(thm)], [c_133, c_1196])).
% 4.76/1.77  tff(c_18, plain, (![A_10, C_18, B_17]: (~r1_orders_2(A_10, C_18, '#skF_1'(A_10, B_17, C_18)) | r1_lattice3(A_10, B_17, C_18) | ~m1_subset_1(C_18, u1_struct_0(A_10)) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.76/1.77  tff(c_1255, plain, (![B_17]: (r1_lattice3('#skF_3', B_17, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | k1_tarski('#skF_1'('#skF_3', B_17, '#skF_7'))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_17, '#skF_7'), '#skF_4'))), inference(resolution, [status(thm)], [c_1247, c_18])).
% 4.76/1.77  tff(c_1281, plain, (![B_327]: (r1_lattice3('#skF_3', B_327, '#skF_7') | k1_tarski('#skF_1'('#skF_3', B_327, '#skF_7'))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_327, '#skF_7'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_1255])).
% 4.76/1.77  tff(c_1285, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r1_lattice3('#skF_3', '#skF_4', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_20, c_1281])).
% 4.76/1.77  tff(c_1288, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_1285])).
% 4.76/1.77  tff(c_1289, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_108, c_1288])).
% 4.76/1.77  tff(c_4, plain, (![A_1]: (~v1_xboole_0(k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.76/1.77  tff(c_1345, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1289, c_4])).
% 4.76/1.77  tff(c_1360, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1345])).
% 4.76/1.77  tff(c_1361, plain, (r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(splitRight, [status(thm)], [c_74])).
% 4.76/1.77  tff(c_1364, plain, (~r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1361, c_68])).
% 4.76/1.77  tff(c_1372, plain, (![A_334, C_335, B_336]: (m1_subset_1(A_334, C_335) | ~m1_subset_1(B_336, k1_zfmisc_1(C_335)) | ~r2_hidden(A_334, B_336))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.76/1.77  tff(c_1384, plain, (![A_334]: (m1_subset_1(A_334, u1_struct_0('#skF_3')) | ~r2_hidden(A_334, '#skF_5'))), inference(resolution, [status(thm)], [c_56, c_1372])).
% 4.76/1.77  tff(c_1461, plain, (![D_353]: (m1_subset_1('#skF_6'(D_353), k1_zfmisc_1('#skF_4')) | ~r2_hidden(D_353, '#skF_5') | ~m1_subset_1(D_353, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.76/1.77  tff(c_1472, plain, (![D_353]: (r1_tarski('#skF_6'(D_353), '#skF_4') | ~r2_hidden(D_353, '#skF_5') | ~m1_subset_1(D_353, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1461, c_8])).
% 4.76/1.77  tff(c_78, plain, (![D_108]: (r2_yellow_0('#skF_3', '#skF_6'(D_108)) | ~r2_hidden(D_108, '#skF_5') | ~m1_subset_1(D_108, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.76/1.77  tff(c_1516, plain, (![A_369, B_370, D_371, C_372]: (r1_lattice3(A_369, B_370, D_371) | ~r1_lattice3(A_369, C_372, D_371) | ~m1_subset_1(D_371, u1_struct_0(A_369)) | ~r1_tarski(B_370, C_372) | ~l1_orders_2(A_369))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.76/1.77  tff(c_1518, plain, (![B_370]: (r1_lattice3('#skF_3', B_370, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_tarski(B_370, '#skF_4') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_1361, c_1516])).
% 4.76/1.77  tff(c_1521, plain, (![B_370]: (r1_lattice3('#skF_3', B_370, '#skF_7') | ~r1_tarski(B_370, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_1518])).
% 4.76/1.77  tff(c_1427, plain, (![D_351]: (k2_yellow_0('#skF_3', '#skF_6'(D_351))=D_351 | ~r2_hidden(D_351, '#skF_5') | ~m1_subset_1(D_351, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_196])).
% 4.76/1.77  tff(c_1441, plain, (![A_334]: (k2_yellow_0('#skF_3', '#skF_6'(A_334))=A_334 | ~r2_hidden(A_334, '#skF_5'))), inference(resolution, [status(thm)], [c_1384, c_1427])).
% 4.76/1.77  tff(c_34, plain, (![A_34, B_35]: (m1_subset_1(k2_yellow_0(A_34, B_35), u1_struct_0(A_34)) | ~l1_orders_2(A_34))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.76/1.77  tff(c_2181, plain, (![A_497, D_498, B_499]: (r1_orders_2(A_497, D_498, k2_yellow_0(A_497, B_499)) | ~r1_lattice3(A_497, B_499, D_498) | ~m1_subset_1(D_498, u1_struct_0(A_497)) | ~r2_yellow_0(A_497, B_499) | ~m1_subset_1(k2_yellow_0(A_497, B_499), u1_struct_0(A_497)) | ~l1_orders_2(A_497))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.76/1.77  tff(c_2207, plain, (![A_500, D_501, B_502]: (r1_orders_2(A_500, D_501, k2_yellow_0(A_500, B_502)) | ~r1_lattice3(A_500, B_502, D_501) | ~m1_subset_1(D_501, u1_struct_0(A_500)) | ~r2_yellow_0(A_500, B_502) | ~l1_orders_2(A_500))), inference(resolution, [status(thm)], [c_34, c_2181])).
% 4.76/1.77  tff(c_2219, plain, (![D_501, A_334]: (r1_orders_2('#skF_3', D_501, A_334) | ~r1_lattice3('#skF_3', '#skF_6'(A_334), D_501) | ~m1_subset_1(D_501, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', '#skF_6'(A_334)) | ~l1_orders_2('#skF_3') | ~r2_hidden(A_334, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1441, c_2207])).
% 4.76/1.77  tff(c_2227, plain, (![D_503, A_504]: (r1_orders_2('#skF_3', D_503, A_504) | ~r1_lattice3('#skF_3', '#skF_6'(A_504), D_503) | ~m1_subset_1(D_503, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', '#skF_6'(A_504)) | ~r2_hidden(A_504, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2219])).
% 4.76/1.77  tff(c_2276, plain, (![A_504]: (r1_orders_2('#skF_3', '#skF_7', A_504) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', '#skF_6'(A_504)) | ~r2_hidden(A_504, '#skF_5') | ~r1_tarski('#skF_6'(A_504), '#skF_4'))), inference(resolution, [status(thm)], [c_1521, c_2227])).
% 4.76/1.77  tff(c_2359, plain, (![A_508]: (r1_orders_2('#skF_3', '#skF_7', A_508) | ~r2_yellow_0('#skF_3', '#skF_6'(A_508)) | ~r2_hidden(A_508, '#skF_5') | ~r1_tarski('#skF_6'(A_508), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2276])).
% 4.76/1.77  tff(c_2368, plain, (![D_509]: (r1_orders_2('#skF_3', '#skF_7', D_509) | ~r1_tarski('#skF_6'(D_509), '#skF_4') | ~r2_hidden(D_509, '#skF_5') | ~m1_subset_1(D_509, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_78, c_2359])).
% 4.76/1.77  tff(c_2386, plain, (![D_514]: (r1_orders_2('#skF_3', '#skF_7', D_514) | ~r2_hidden(D_514, '#skF_5') | ~m1_subset_1(D_514, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1472, c_2368])).
% 4.76/1.77  tff(c_2437, plain, (![A_515]: (r1_orders_2('#skF_3', '#skF_7', A_515) | ~r2_hidden(A_515, '#skF_5'))), inference(resolution, [status(thm)], [c_1384, c_2386])).
% 4.76/1.77  tff(c_2445, plain, (![B_17]: (r1_lattice3('#skF_3', B_17, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_17, '#skF_7'), '#skF_5'))), inference(resolution, [status(thm)], [c_2437, c_18])).
% 4.76/1.77  tff(c_2455, plain, (![B_516]: (r1_lattice3('#skF_3', B_516, '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', B_516, '#skF_7'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_2445])).
% 4.76/1.77  tff(c_2459, plain, (r1_lattice3('#skF_3', '#skF_5', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_20, c_2455])).
% 4.76/1.77  tff(c_2462, plain, (r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_2459])).
% 4.76/1.77  tff(c_2464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1364, c_2462])).
% 4.76/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.77  
% 4.76/1.77  Inference rules
% 4.76/1.77  ----------------------
% 4.76/1.77  #Ref     : 0
% 4.76/1.77  #Sup     : 485
% 4.76/1.77  #Fact    : 0
% 4.76/1.77  #Define  : 0
% 4.76/1.77  #Split   : 15
% 4.76/1.77  #Chain   : 0
% 4.76/1.77  #Close   : 0
% 4.76/1.77  
% 4.76/1.77  Ordering : KBO
% 4.76/1.77  
% 4.76/1.77  Simplification rules
% 4.76/1.77  ----------------------
% 4.76/1.77  #Subsume      : 113
% 4.76/1.77  #Demod        : 241
% 4.76/1.77  #Tautology    : 24
% 4.76/1.77  #SimpNegUnit  : 7
% 4.76/1.77  #BackRed      : 0
% 4.76/1.77  
% 4.76/1.77  #Partial instantiations: 0
% 4.76/1.77  #Strategies tried      : 1
% 4.76/1.77  
% 4.76/1.77  Timing (in seconds)
% 4.76/1.77  ----------------------
% 4.76/1.77  Preprocessing        : 0.36
% 4.76/1.77  Parsing              : 0.20
% 4.76/1.77  CNF conversion       : 0.03
% 4.76/1.77  Main loop            : 0.80
% 4.76/1.77  Inferencing          : 0.30
% 4.76/1.77  Reduction            : 0.23
% 4.76/1.77  Demodulation         : 0.15
% 4.76/1.77  BG Simplification    : 0.04
% 4.76/1.78  Subsumption          : 0.17
% 4.76/1.78  Abstraction          : 0.03
% 4.76/1.78  MUC search           : 0.00
% 4.76/1.78  Cooper               : 0.00
% 4.76/1.78  Total                : 1.21
% 4.76/1.78  Index Insertion      : 0.00
% 4.76/1.78  Index Deletion       : 0.00
% 4.76/1.78  Index Matching       : 0.00
% 4.76/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
