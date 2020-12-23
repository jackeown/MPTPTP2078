%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1651+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:11 EST 2020

% Result     : Theorem 51.92s
% Output     : CNFRefutation 52.23s
% Verified   : 
% Statistics : Number of formulae       :  320 (15666 expanded)
%              Number of leaves         :   30 (5109 expanded)
%              Depth                    :   34
%              Number of atoms          : 1209 (73639 expanded)
%              Number of equality atoms :   94 (4503 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r2_hidden > m1_subset_1 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_waybel_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_waybel_0,type,(
    k3_waybel_0: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r2_lattice3(A,B,C)
                <=> r2_lattice3(A,k3_waybel_0(A,B),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_waybel_0)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k3_waybel_0(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_waybel_0)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = k3_waybel_0(A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r2_hidden(D,C)
                    <=> ? [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                          & r1_orders_2(A,D,E)
                          & r2_hidden(E,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_waybel_0)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_113,axiom,(
    ! [A] :
      ( ( v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( r1_orders_2(A,B,C)
                      & r1_orders_2(A,C,D) )
                   => r1_orders_2(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(c_66,plain,
    ( r2_lattice3('#skF_5','#skF_6','#skF_7')
    | r2_lattice3('#skF_5',k3_waybel_0('#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_67,plain,(
    r2_lattice3('#skF_5',k3_waybel_0('#skF_5','#skF_6'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_60,plain,
    ( ~ r2_lattice3('#skF_5',k3_waybel_0('#skF_5','#skF_6'),'#skF_7')
    | ~ r2_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_73,plain,(
    ~ r2_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_60])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_52,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_34,plain,(
    ! [A_85,B_92,C_93] :
      ( m1_subset_1('#skF_4'(A_85,B_92,C_93),u1_struct_0(A_85))
      | r2_lattice3(A_85,B_92,C_93)
      | ~ m1_subset_1(C_93,u1_struct_0(A_85))
      | ~ l1_orders_2(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_36,plain,(
    ! [A_97,B_98] :
      ( m1_subset_1(k3_waybel_0(A_97,B_98),k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_orders_2(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_307,plain,(
    ! [A_191,B_192,C_193] :
      ( r2_hidden('#skF_2'(A_191,B_192,C_193),C_193)
      | r2_hidden('#skF_3'(A_191,B_192,C_193),B_192)
      | k3_waybel_0(A_191,B_192) = C_193
      | ~ m1_subset_1(C_193,k1_zfmisc_1(u1_struct_0(A_191)))
      | ~ m1_subset_1(B_192,k1_zfmisc_1(u1_struct_0(A_191)))
      | ~ l1_orders_2(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_311,plain,(
    ! [B_192] :
      ( r2_hidden('#skF_2'('#skF_5',B_192,'#skF_6'),'#skF_6')
      | r2_hidden('#skF_3'('#skF_5',B_192,'#skF_6'),B_192)
      | k3_waybel_0('#skF_5',B_192) = '#skF_6'
      | ~ m1_subset_1(B_192,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_307])).

tff(c_316,plain,(
    ! [B_194] :
      ( r2_hidden('#skF_2'('#skF_5',B_194,'#skF_6'),'#skF_6')
      | r2_hidden('#skF_3'('#skF_5',B_194,'#skF_6'),B_194)
      | k3_waybel_0('#skF_5',B_194) = '#skF_6'
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_311])).

tff(c_325,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_6')
    | r2_hidden('#skF_3'('#skF_5','#skF_6','#skF_6'),'#skF_6')
    | k3_waybel_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_50,c_316])).

tff(c_326,plain,(
    k3_waybel_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_325])).

tff(c_327,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_67])).

tff(c_329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_327])).

tff(c_331,plain,(
    k3_waybel_0('#skF_5','#skF_6') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_325])).

tff(c_330,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6','#skF_6'),'#skF_6')
    | r2_hidden('#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_325])).

tff(c_368,plain,(
    r2_hidden('#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_330])).

tff(c_2,plain,(
    ! [A_1,B_45,C_67] :
      ( m1_subset_1('#skF_2'(A_1,B_45,C_67),u1_struct_0(A_1))
      | k3_waybel_0(A_1,B_45) = C_67
      | ~ m1_subset_1(C_67,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_54,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_68,plain,(
    ! [A_127,C_128,B_129] :
      ( m1_subset_1(A_127,C_128)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(C_128))
      | ~ r2_hidden(A_127,B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_71,plain,(
    ! [A_127] :
      ( m1_subset_1(A_127,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_127,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_50,c_68])).

tff(c_28,plain,(
    ! [A_85,D_96,C_93,B_92] :
      ( r1_orders_2(A_85,D_96,C_93)
      | ~ r2_hidden(D_96,B_92)
      | ~ m1_subset_1(D_96,u1_struct_0(A_85))
      | ~ r2_lattice3(A_85,B_92,C_93)
      | ~ m1_subset_1(C_93,u1_struct_0(A_85))
      | ~ l1_orders_2(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_378,plain,(
    ! [A_200,C_201] :
      ( r1_orders_2(A_200,'#skF_2'('#skF_5','#skF_6','#skF_6'),C_201)
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_6'),u1_struct_0(A_200))
      | ~ r2_lattice3(A_200,'#skF_6',C_201)
      | ~ m1_subset_1(C_201,u1_struct_0(A_200))
      | ~ l1_orders_2(A_200) ) ),
    inference(resolution,[status(thm)],[c_368,c_28])).

tff(c_384,plain,(
    ! [C_201] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_6'),C_201)
      | ~ r2_lattice3('#skF_5','#skF_6',C_201)
      | ~ m1_subset_1(C_201,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ r2_hidden('#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_71,c_378])).

tff(c_392,plain,(
    ! [C_202] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_6'),C_202)
      | ~ r2_lattice3('#skF_5','#skF_6',C_202)
      | ~ m1_subset_1(C_202,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_52,c_384])).

tff(c_44,plain,(
    ! [A_105,B_113,D_119,C_117] :
      ( r1_orders_2(A_105,B_113,D_119)
      | ~ r1_orders_2(A_105,C_117,D_119)
      | ~ r1_orders_2(A_105,B_113,C_117)
      | ~ m1_subset_1(D_119,u1_struct_0(A_105))
      | ~ m1_subset_1(C_117,u1_struct_0(A_105))
      | ~ m1_subset_1(B_113,u1_struct_0(A_105))
      | ~ l1_orders_2(A_105)
      | ~ v4_orders_2(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_394,plain,(
    ! [B_113,C_202] :
      ( r1_orders_2('#skF_5',B_113,C_202)
      | ~ r1_orders_2('#skF_5',B_113,'#skF_2'('#skF_5','#skF_6','#skF_6'))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_113,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ r2_lattice3('#skF_5','#skF_6',C_202)
      | ~ m1_subset_1(C_202,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_392,c_44])).

tff(c_397,plain,(
    ! [B_113,C_202] :
      ( r1_orders_2('#skF_5',B_113,C_202)
      | ~ r1_orders_2('#skF_5',B_113,'#skF_2'('#skF_5','#skF_6','#skF_6'))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_113,u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5','#skF_6',C_202)
      | ~ m1_subset_1(C_202,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_394])).

tff(c_545,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_397])).

tff(c_552,plain,
    ( k3_waybel_0('#skF_5','#skF_6') = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_545])).

tff(c_558,plain,(
    k3_waybel_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_552])).

tff(c_560,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_331,c_558])).

tff(c_562,plain,(
    m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_397])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_56,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_87,plain,(
    ! [A_145,B_146,C_147] :
      ( r3_orders_2(A_145,B_146,B_146)
      | ~ m1_subset_1(C_147,u1_struct_0(A_145))
      | ~ m1_subset_1(B_146,u1_struct_0(A_145))
      | ~ l1_orders_2(A_145)
      | ~ v3_orders_2(A_145)
      | v2_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_93,plain,(
    ! [B_146] :
      ( r3_orders_2('#skF_5',B_146,B_146)
      | ~ m1_subset_1(B_146,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_87])).

tff(c_101,plain,(
    ! [B_146] :
      ( r3_orders_2('#skF_5',B_146,B_146)
      | ~ m1_subset_1(B_146,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_93])).

tff(c_102,plain,(
    ! [B_146] :
      ( r3_orders_2('#skF_5',B_146,B_146)
      | ~ m1_subset_1(B_146,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_101])).

tff(c_597,plain,(
    r3_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_2'('#skF_5','#skF_6','#skF_6')) ),
    inference(resolution,[status(thm)],[c_562,c_102])).

tff(c_40,plain,(
    ! [A_99,B_100,C_101] :
      ( r1_orders_2(A_99,B_100,C_101)
      | ~ r3_orders_2(A_99,B_100,C_101)
      | ~ m1_subset_1(C_101,u1_struct_0(A_99))
      | ~ m1_subset_1(B_100,u1_struct_0(A_99))
      | ~ l1_orders_2(A_99)
      | ~ v3_orders_2(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_603,plain,
    ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_2'('#skF_5','#skF_6','#skF_6'))
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_597,c_40])).

tff(c_606,plain,
    ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_2'('#skF_5','#skF_6','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_562,c_603])).

tff(c_607,plain,(
    r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_2'('#skF_5','#skF_6','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_606])).

tff(c_1045,plain,(
    ! [E_298,B_299,A_300,C_301] :
      ( ~ r2_hidden(E_298,B_299)
      | ~ r1_orders_2(A_300,'#skF_2'(A_300,B_299,C_301),E_298)
      | ~ m1_subset_1(E_298,u1_struct_0(A_300))
      | ~ r2_hidden('#skF_2'(A_300,B_299,C_301),C_301)
      | k3_waybel_0(A_300,B_299) = C_301
      | ~ m1_subset_1(C_301,k1_zfmisc_1(u1_struct_0(A_300)))
      | ~ m1_subset_1(B_299,k1_zfmisc_1(u1_struct_0(A_300)))
      | ~ l1_orders_2(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1050,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_6')
    | k3_waybel_0('#skF_5','#skF_6') = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_607,c_1045])).

tff(c_1063,plain,(
    k3_waybel_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_368,c_562,c_1050])).

tff(c_1065,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_331,c_1063])).

tff(c_1067,plain,(
    ~ r2_hidden('#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_18,plain,(
    ! [A_1,B_45,C_67] :
      ( r2_hidden('#skF_2'(A_1,B_45,C_67),C_67)
      | m1_subset_1('#skF_3'(A_1,B_45,C_67),u1_struct_0(A_1))
      | k3_waybel_0(A_1,B_45) = C_67
      | ~ m1_subset_1(C_67,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1066,plain,(
    r2_hidden('#skF_3'('#skF_5','#skF_6','#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_330])).

tff(c_1072,plain,(
    ! [A_302,C_303] :
      ( r1_orders_2(A_302,'#skF_3'('#skF_5','#skF_6','#skF_6'),C_303)
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6','#skF_6'),u1_struct_0(A_302))
      | ~ r2_lattice3(A_302,'#skF_6',C_303)
      | ~ m1_subset_1(C_303,u1_struct_0(A_302))
      | ~ l1_orders_2(A_302) ) ),
    inference(resolution,[status(thm)],[c_1066,c_28])).

tff(c_1075,plain,(
    ! [C_303] :
      ( r1_orders_2('#skF_5','#skF_3'('#skF_5','#skF_6','#skF_6'),C_303)
      | ~ r2_lattice3('#skF_5','#skF_6',C_303)
      | ~ m1_subset_1(C_303,u1_struct_0('#skF_5'))
      | r2_hidden('#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_6')
      | k3_waybel_0('#skF_5','#skF_6') = '#skF_6'
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_18,c_1072])).

tff(c_1081,plain,(
    ! [C_303] :
      ( r1_orders_2('#skF_5','#skF_3'('#skF_5','#skF_6','#skF_6'),C_303)
      | ~ r2_lattice3('#skF_5','#skF_6',C_303)
      | ~ m1_subset_1(C_303,u1_struct_0('#skF_5'))
      | r2_hidden('#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_6')
      | k3_waybel_0('#skF_5','#skF_6') = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1075])).

tff(c_1092,plain,(
    ! [C_306] :
      ( r1_orders_2('#skF_5','#skF_3'('#skF_5','#skF_6','#skF_6'),C_306)
      | ~ r2_lattice3('#skF_5','#skF_6',C_306)
      | ~ m1_subset_1(C_306,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_331,c_1067,c_1081])).

tff(c_1094,plain,(
    ! [B_113,C_306] :
      ( r1_orders_2('#skF_5',B_113,C_306)
      | ~ r1_orders_2('#skF_5',B_113,'#skF_3'('#skF_5','#skF_6','#skF_6'))
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_113,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ r2_lattice3('#skF_5','#skF_6',C_306)
      | ~ m1_subset_1(C_306,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_1092,c_44])).

tff(c_1097,plain,(
    ! [B_113,C_306] :
      ( r1_orders_2('#skF_5',B_113,C_306)
      | ~ r1_orders_2('#skF_5',B_113,'#skF_3'('#skF_5','#skF_6','#skF_6'))
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_113,u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5','#skF_6',C_306)
      | ~ m1_subset_1(C_306,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1094])).

tff(c_3657,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1097])).

tff(c_3660,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_6')
    | k3_waybel_0('#skF_5','#skF_6') = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_3657])).

tff(c_3666,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_6')
    | k3_waybel_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_3660])).

tff(c_3668,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_331,c_1067,c_3666])).

tff(c_3670,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1097])).

tff(c_332,plain,(
    ! [A_195,B_196,C_197] :
      ( r2_hidden('#skF_2'(A_195,B_196,C_197),C_197)
      | m1_subset_1('#skF_3'(A_195,B_196,C_197),u1_struct_0(A_195))
      | k3_waybel_0(A_195,B_196) = C_197
      | ~ m1_subset_1(C_197,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ l1_orders_2(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_351,plain,(
    ! [B_196,C_197] :
      ( r3_orders_2('#skF_5','#skF_3'('#skF_5',B_196,C_197),'#skF_3'('#skF_5',B_196,C_197))
      | r2_hidden('#skF_2'('#skF_5',B_196,C_197),C_197)
      | k3_waybel_0('#skF_5',B_196) = C_197
      | ~ m1_subset_1(C_197,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_332,c_102])).

tff(c_3650,plain,(
    ! [B_546,C_547] :
      ( r3_orders_2('#skF_5','#skF_3'('#skF_5',B_546,C_547),'#skF_3'('#skF_5',B_546,C_547))
      | r2_hidden('#skF_2'('#skF_5',B_546,C_547),C_547)
      | k3_waybel_0('#skF_5',B_546) = C_547
      | ~ m1_subset_1(C_547,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_546,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_351])).

tff(c_3652,plain,(
    ! [B_546,C_547] :
      ( r1_orders_2('#skF_5','#skF_3'('#skF_5',B_546,C_547),'#skF_3'('#skF_5',B_546,C_547))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_546,C_547),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | r2_hidden('#skF_2'('#skF_5',B_546,C_547),C_547)
      | k3_waybel_0('#skF_5',B_546) = C_547
      | ~ m1_subset_1(C_547,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_546,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_3650,c_40])).

tff(c_3655,plain,(
    ! [B_546,C_547] :
      ( r1_orders_2('#skF_5','#skF_3'('#skF_5',B_546,C_547),'#skF_3'('#skF_5',B_546,C_547))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_546,C_547),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | r2_hidden('#skF_2'('#skF_5',B_546,C_547),C_547)
      | k3_waybel_0('#skF_5',B_546) = C_547
      | ~ m1_subset_1(C_547,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_546,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_3652])).

tff(c_3656,plain,(
    ! [B_546,C_547] :
      ( r1_orders_2('#skF_5','#skF_3'('#skF_5',B_546,C_547),'#skF_3'('#skF_5',B_546,C_547))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_546,C_547),u1_struct_0('#skF_5'))
      | r2_hidden('#skF_2'('#skF_5',B_546,C_547),C_547)
      | k3_waybel_0('#skF_5',B_546) = C_547
      | ~ m1_subset_1(C_547,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_546,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3655])).

tff(c_5932,plain,(
    ! [D_742,A_743,B_744,E_745] :
      ( r2_hidden(D_742,k3_waybel_0(A_743,B_744))
      | ~ r2_hidden(E_745,B_744)
      | ~ r1_orders_2(A_743,D_742,E_745)
      | ~ m1_subset_1(E_745,u1_struct_0(A_743))
      | ~ m1_subset_1(D_742,u1_struct_0(A_743))
      | ~ m1_subset_1(k3_waybel_0(A_743,B_744),k1_zfmisc_1(u1_struct_0(A_743)))
      | ~ m1_subset_1(B_744,k1_zfmisc_1(u1_struct_0(A_743)))
      | ~ l1_orders_2(A_743) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_7000,plain,(
    ! [D_876,A_877] :
      ( r2_hidden(D_876,k3_waybel_0(A_877,'#skF_6'))
      | ~ r1_orders_2(A_877,D_876,'#skF_3'('#skF_5','#skF_6','#skF_6'))
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6','#skF_6'),u1_struct_0(A_877))
      | ~ m1_subset_1(D_876,u1_struct_0(A_877))
      | ~ m1_subset_1(k3_waybel_0(A_877,'#skF_6'),k1_zfmisc_1(u1_struct_0(A_877)))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_877)))
      | ~ l1_orders_2(A_877) ) ),
    inference(resolution,[status(thm)],[c_1066,c_5932])).

tff(c_7012,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6','#skF_6'),k3_waybel_0('#skF_5','#skF_6'))
    | ~ m1_subset_1(k3_waybel_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5'))
    | r2_hidden('#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_6')
    | k3_waybel_0('#skF_5','#skF_6') = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_3656,c_7000])).

tff(c_7037,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6','#skF_6'),k3_waybel_0('#skF_5','#skF_6'))
    | ~ m1_subset_1(k3_waybel_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | r2_hidden('#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_6')
    | k3_waybel_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_3670,c_52,c_7012])).

tff(c_7038,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6','#skF_6'),k3_waybel_0('#skF_5','#skF_6'))
    | ~ m1_subset_1(k3_waybel_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_331,c_1067,c_7037])).

tff(c_7065,plain,(
    ~ m1_subset_1(k3_waybel_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_7038])).

tff(c_7068,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_7065])).

tff(c_7072,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_7068])).

tff(c_7074,plain,(
    m1_subset_1(k3_waybel_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_7038])).

tff(c_103,plain,(
    ! [B_148] :
      ( r3_orders_2('#skF_5',B_148,B_148)
      | ~ m1_subset_1(B_148,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_101])).

tff(c_106,plain,(
    ! [B_92,C_93] :
      ( r3_orders_2('#skF_5','#skF_4'('#skF_5',B_92,C_93),'#skF_4'('#skF_5',B_92,C_93))
      | r2_lattice3('#skF_5',B_92,C_93)
      | ~ m1_subset_1(C_93,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_103])).

tff(c_113,plain,(
    ! [B_92,C_93] :
      ( r3_orders_2('#skF_5','#skF_4'('#skF_5',B_92,C_93),'#skF_4'('#skF_5',B_92,C_93))
      | r2_lattice3('#skF_5',B_92,C_93)
      | ~ m1_subset_1(C_93,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_106])).

tff(c_122,plain,(
    ! [A_156,B_157,C_158] :
      ( r1_orders_2(A_156,B_157,C_158)
      | ~ r3_orders_2(A_156,B_157,C_158)
      | ~ m1_subset_1(C_158,u1_struct_0(A_156))
      | ~ m1_subset_1(B_157,u1_struct_0(A_156))
      | ~ l1_orders_2(A_156)
      | ~ v3_orders_2(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_124,plain,(
    ! [B_92,C_93] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_5',B_92,C_93),'#skF_4'('#skF_5',B_92,C_93))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_92,C_93),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | r2_lattice3('#skF_5',B_92,C_93)
      | ~ m1_subset_1(C_93,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_113,c_122])).

tff(c_131,plain,(
    ! [B_92,C_93] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_5',B_92,C_93),'#skF_4'('#skF_5',B_92,C_93))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_92,C_93),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | r2_lattice3('#skF_5',B_92,C_93)
      | ~ m1_subset_1(C_93,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_124])).

tff(c_132,plain,(
    ! [B_92,C_93] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_5',B_92,C_93),'#skF_4'('#skF_5',B_92,C_93))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_92,C_93),u1_struct_0('#skF_5'))
      | r2_lattice3('#skF_5',B_92,C_93)
      | ~ m1_subset_1(C_93,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_131])).

tff(c_32,plain,(
    ! [A_85,B_92,C_93] :
      ( r2_hidden('#skF_4'(A_85,B_92,C_93),B_92)
      | r2_lattice3(A_85,B_92,C_93)
      | ~ m1_subset_1(C_93,u1_struct_0(A_85))
      | ~ l1_orders_2(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_7225,plain,(
    ! [D_886,C_888,A_889,A_885,B_887] :
      ( r2_hidden(D_886,k3_waybel_0(A_885,B_887))
      | ~ r1_orders_2(A_885,D_886,'#skF_4'(A_889,B_887,C_888))
      | ~ m1_subset_1('#skF_4'(A_889,B_887,C_888),u1_struct_0(A_885))
      | ~ m1_subset_1(D_886,u1_struct_0(A_885))
      | ~ m1_subset_1(k3_waybel_0(A_885,B_887),k1_zfmisc_1(u1_struct_0(A_885)))
      | ~ m1_subset_1(B_887,k1_zfmisc_1(u1_struct_0(A_885)))
      | ~ l1_orders_2(A_885)
      | r2_lattice3(A_889,B_887,C_888)
      | ~ m1_subset_1(C_888,u1_struct_0(A_889))
      | ~ l1_orders_2(A_889) ) ),
    inference(resolution,[status(thm)],[c_32,c_5932])).

tff(c_7241,plain,(
    ! [B_92,C_93] :
      ( r2_hidden('#skF_4'('#skF_5',B_92,C_93),k3_waybel_0('#skF_5',B_92))
      | ~ m1_subset_1(k3_waybel_0('#skF_5',B_92),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ m1_subset_1('#skF_4'('#skF_5',B_92,C_93),u1_struct_0('#skF_5'))
      | r2_lattice3('#skF_5',B_92,C_93)
      | ~ m1_subset_1(C_93,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_132,c_7225])).

tff(c_21046,plain,(
    ! [B_1614,C_1615] :
      ( r2_hidden('#skF_4'('#skF_5',B_1614,C_1615),k3_waybel_0('#skF_5',B_1614))
      | ~ m1_subset_1(k3_waybel_0('#skF_5',B_1614),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1614,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_1614,C_1615),u1_struct_0('#skF_5'))
      | r2_lattice3('#skF_5',B_1614,C_1615)
      | ~ m1_subset_1(C_1615,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_7241])).

tff(c_21050,plain,(
    ! [C_1615] :
      ( r2_hidden('#skF_4'('#skF_5','#skF_6',C_1615),k3_waybel_0('#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6',C_1615),u1_struct_0('#skF_5'))
      | r2_lattice3('#skF_5','#skF_6',C_1615)
      | ~ m1_subset_1(C_1615,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_7074,c_21046])).

tff(c_21062,plain,(
    ! [C_1616] :
      ( r2_hidden('#skF_4'('#skF_5','#skF_6',C_1616),k3_waybel_0('#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6',C_1616),u1_struct_0('#skF_5'))
      | r2_lattice3('#skF_5','#skF_6',C_1616)
      | ~ m1_subset_1(C_1616,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_21050])).

tff(c_24856,plain,(
    ! [A_1853,C_1854,C_1855] :
      ( r1_orders_2(A_1853,'#skF_4'('#skF_5','#skF_6',C_1854),C_1855)
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6',C_1854),u1_struct_0(A_1853))
      | ~ r2_lattice3(A_1853,k3_waybel_0('#skF_5','#skF_6'),C_1855)
      | ~ m1_subset_1(C_1855,u1_struct_0(A_1853))
      | ~ l1_orders_2(A_1853)
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6',C_1854),u1_struct_0('#skF_5'))
      | r2_lattice3('#skF_5','#skF_6',C_1854)
      | ~ m1_subset_1(C_1854,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_21062,c_28])).

tff(c_24859,plain,(
    ! [C_93,C_1855] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_5','#skF_6',C_93),C_1855)
      | ~ r2_lattice3('#skF_5',k3_waybel_0('#skF_5','#skF_6'),C_1855)
      | ~ m1_subset_1(C_1855,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6',C_93),u1_struct_0('#skF_5'))
      | r2_lattice3('#skF_5','#skF_6',C_93)
      | ~ m1_subset_1(C_93,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_24856])).

tff(c_24869,plain,(
    ! [C_1856,C_1857] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_5','#skF_6',C_1856),C_1857)
      | ~ r2_lattice3('#skF_5',k3_waybel_0('#skF_5','#skF_6'),C_1857)
      | ~ m1_subset_1(C_1857,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6',C_1856),u1_struct_0('#skF_5'))
      | r2_lattice3('#skF_5','#skF_6',C_1856)
      | ~ m1_subset_1(C_1856,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_24859])).

tff(c_24874,plain,(
    ! [C_1856] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_5','#skF_6',C_1856),'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6',C_1856),u1_struct_0('#skF_5'))
      | r2_lattice3('#skF_5','#skF_6',C_1856)
      | ~ m1_subset_1(C_1856,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_67,c_24869])).

tff(c_24882,plain,(
    ! [C_1858] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_5','#skF_6',C_1858),'#skF_7')
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6',C_1858),u1_struct_0('#skF_5'))
      | r2_lattice3('#skF_5','#skF_6',C_1858)
      | ~ m1_subset_1(C_1858,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_24874])).

tff(c_24886,plain,(
    ! [C_93] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_5','#skF_6',C_93),'#skF_7')
      | r2_lattice3('#skF_5','#skF_6',C_93)
      | ~ m1_subset_1(C_93,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_24882])).

tff(c_24910,plain,(
    ! [C_1864] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_5','#skF_6',C_1864),'#skF_7')
      | r2_lattice3('#skF_5','#skF_6',C_1864)
      | ~ m1_subset_1(C_1864,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_24886])).

tff(c_30,plain,(
    ! [A_85,B_92,C_93] :
      ( ~ r1_orders_2(A_85,'#skF_4'(A_85,B_92,C_93),C_93)
      | r2_lattice3(A_85,B_92,C_93)
      | ~ m1_subset_1(C_93,u1_struct_0(A_85))
      | ~ l1_orders_2(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_24916,plain,
    ( ~ l1_orders_2('#skF_5')
    | r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_24910,c_30])).

tff(c_24922,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52,c_24916])).

tff(c_24924,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_24922])).

tff(c_24926,plain,(
    ~ r2_lattice3('#skF_5',k3_waybel_0('#skF_5','#skF_6'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_24925,plain,(
    r2_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_25166,plain,(
    ! [A_1929,B_1930,C_1931] :
      ( r2_hidden('#skF_2'(A_1929,B_1930,C_1931),C_1931)
      | r2_hidden('#skF_3'(A_1929,B_1930,C_1931),B_1930)
      | k3_waybel_0(A_1929,B_1930) = C_1931
      | ~ m1_subset_1(C_1931,k1_zfmisc_1(u1_struct_0(A_1929)))
      | ~ m1_subset_1(B_1930,k1_zfmisc_1(u1_struct_0(A_1929)))
      | ~ l1_orders_2(A_1929) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_25170,plain,(
    ! [B_1930] :
      ( r2_hidden('#skF_2'('#skF_5',B_1930,'#skF_6'),'#skF_6')
      | r2_hidden('#skF_3'('#skF_5',B_1930,'#skF_6'),B_1930)
      | k3_waybel_0('#skF_5',B_1930) = '#skF_6'
      | ~ m1_subset_1(B_1930,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_25166])).

tff(c_25175,plain,(
    ! [B_1932] :
      ( r2_hidden('#skF_2'('#skF_5',B_1932,'#skF_6'),'#skF_6')
      | r2_hidden('#skF_3'('#skF_5',B_1932,'#skF_6'),B_1932)
      | k3_waybel_0('#skF_5',B_1932) = '#skF_6'
      | ~ m1_subset_1(B_1932,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_25170])).

tff(c_25184,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_6')
    | r2_hidden('#skF_3'('#skF_5','#skF_6','#skF_6'),'#skF_6')
    | k3_waybel_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_50,c_25175])).

tff(c_25185,plain,(
    k3_waybel_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_25184])).

tff(c_25222,plain,(
    ~ r2_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25185,c_24926])).

tff(c_25225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24925,c_25222])).

tff(c_25227,plain,(
    k3_waybel_0('#skF_5','#skF_6') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_25184])).

tff(c_25226,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6','#skF_6'),'#skF_6')
    | r2_hidden('#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_25184])).

tff(c_25228,plain,(
    r2_hidden('#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_25226])).

tff(c_25238,plain,(
    ! [A_1938,C_1939] :
      ( r1_orders_2(A_1938,'#skF_2'('#skF_5','#skF_6','#skF_6'),C_1939)
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_6'),u1_struct_0(A_1938))
      | ~ r2_lattice3(A_1938,'#skF_6',C_1939)
      | ~ m1_subset_1(C_1939,u1_struct_0(A_1938))
      | ~ l1_orders_2(A_1938) ) ),
    inference(resolution,[status(thm)],[c_25228,c_28])).

tff(c_25241,plain,(
    ! [C_1939] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_6'),C_1939)
      | ~ r2_lattice3('#skF_5','#skF_6',C_1939)
      | ~ m1_subset_1(C_1939,u1_struct_0('#skF_5'))
      | k3_waybel_0('#skF_5','#skF_6') = '#skF_6'
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2,c_25238])).

tff(c_25247,plain,(
    ! [C_1939] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_6'),C_1939)
      | ~ r2_lattice3('#skF_5','#skF_6',C_1939)
      | ~ m1_subset_1(C_1939,u1_struct_0('#skF_5'))
      | k3_waybel_0('#skF_5','#skF_6') = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_25241])).

tff(c_25248,plain,(
    ! [C_1939] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_6'),C_1939)
      | ~ r2_lattice3('#skF_5','#skF_6',C_1939)
      | ~ m1_subset_1(C_1939,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_25227,c_25247])).

tff(c_25099,plain,(
    ! [A_1913,B_1914,C_1915] :
      ( m1_subset_1('#skF_2'(A_1913,B_1914,C_1915),u1_struct_0(A_1913))
      | k3_waybel_0(A_1913,B_1914) = C_1915
      | ~ m1_subset_1(C_1915,k1_zfmisc_1(u1_struct_0(A_1913)))
      | ~ m1_subset_1(B_1914,k1_zfmisc_1(u1_struct_0(A_1913)))
      | ~ l1_orders_2(A_1913) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24981,plain,(
    ! [A_1894,B_1895,C_1896] :
      ( r3_orders_2(A_1894,B_1895,C_1896)
      | ~ r1_orders_2(A_1894,B_1895,C_1896)
      | ~ m1_subset_1(C_1896,u1_struct_0(A_1894))
      | ~ m1_subset_1(B_1895,u1_struct_0(A_1894))
      | ~ l1_orders_2(A_1894)
      | ~ v3_orders_2(A_1894)
      | v2_struct_0(A_1894) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24987,plain,(
    ! [B_1895] :
      ( r3_orders_2('#skF_5',B_1895,'#skF_7')
      | ~ r1_orders_2('#skF_5',B_1895,'#skF_7')
      | ~ m1_subset_1(B_1895,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_24981])).

tff(c_24995,plain,(
    ! [B_1895] :
      ( r3_orders_2('#skF_5',B_1895,'#skF_7')
      | ~ r1_orders_2('#skF_5',B_1895,'#skF_7')
      | ~ m1_subset_1(B_1895,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_24987])).

tff(c_24996,plain,(
    ! [B_1895] :
      ( r3_orders_2('#skF_5',B_1895,'#skF_7')
      | ~ r1_orders_2('#skF_5',B_1895,'#skF_7')
      | ~ m1_subset_1(B_1895,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_24995])).

tff(c_25108,plain,(
    ! [B_1914,C_1915] :
      ( r3_orders_2('#skF_5','#skF_2'('#skF_5',B_1914,C_1915),'#skF_7')
      | ~ r1_orders_2('#skF_5','#skF_2'('#skF_5',B_1914,C_1915),'#skF_7')
      | k3_waybel_0('#skF_5',B_1914) = C_1915
      | ~ m1_subset_1(C_1915,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1914,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_25099,c_24996])).

tff(c_25316,plain,(
    ! [B_1948,C_1949] :
      ( r3_orders_2('#skF_5','#skF_2'('#skF_5',B_1948,C_1949),'#skF_7')
      | ~ r1_orders_2('#skF_5','#skF_2'('#skF_5',B_1948,C_1949),'#skF_7')
      | k3_waybel_0('#skF_5',B_1948) = C_1949
      | ~ m1_subset_1(C_1949,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1948,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_25108])).

tff(c_25326,plain,(
    ! [B_1950] :
      ( r3_orders_2('#skF_5','#skF_2'('#skF_5',B_1950,'#skF_6'),'#skF_7')
      | ~ r1_orders_2('#skF_5','#skF_2'('#skF_5',B_1950,'#skF_6'),'#skF_7')
      | k3_waybel_0('#skF_5',B_1950) = '#skF_6'
      | ~ m1_subset_1(B_1950,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_50,c_25316])).

tff(c_25333,plain,
    ( r3_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_7')
    | ~ r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_7')
    | k3_waybel_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_50,c_25326])).

tff(c_25339,plain,
    ( r3_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_7')
    | ~ r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_25227,c_25333])).

tff(c_25340,plain,(
    ~ r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_25339])).

tff(c_25343,plain,
    ( ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_25248,c_25340])).

tff(c_25347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_24925,c_25343])).

tff(c_25349,plain,(
    r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_25339])).

tff(c_25357,plain,(
    ! [B_113] :
      ( r1_orders_2('#skF_5',B_113,'#skF_7')
      | ~ r1_orders_2('#skF_5',B_113,'#skF_2'('#skF_5','#skF_6','#skF_6'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_113,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_25349,c_44])).

tff(c_25360,plain,(
    ! [B_113] :
      ( r1_orders_2('#skF_5',B_113,'#skF_7')
      | ~ r1_orders_2('#skF_5',B_113,'#skF_2'('#skF_5','#skF_6','#skF_6'))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_113,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_25357])).

tff(c_25362,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_25360])).

tff(c_25365,plain,
    ( k3_waybel_0('#skF_5','#skF_6') = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_25362])).

tff(c_25371,plain,(
    k3_waybel_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_25365])).

tff(c_25373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25227,c_25371])).

tff(c_25375,plain,(
    m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_25360])).

tff(c_24946,plain,(
    ! [A_1883,B_1884,C_1885] :
      ( r3_orders_2(A_1883,B_1884,B_1884)
      | ~ m1_subset_1(C_1885,u1_struct_0(A_1883))
      | ~ m1_subset_1(B_1884,u1_struct_0(A_1883))
      | ~ l1_orders_2(A_1883)
      | ~ v3_orders_2(A_1883)
      | v2_struct_0(A_1883) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_24952,plain,(
    ! [B_1884] :
      ( r3_orders_2('#skF_5',B_1884,B_1884)
      | ~ m1_subset_1(B_1884,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_24946])).

tff(c_24960,plain,(
    ! [B_1884] :
      ( r3_orders_2('#skF_5',B_1884,B_1884)
      | ~ m1_subset_1(B_1884,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_24952])).

tff(c_24961,plain,(
    ! [B_1884] :
      ( r3_orders_2('#skF_5',B_1884,B_1884)
      | ~ m1_subset_1(B_1884,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_24960])).

tff(c_25416,plain,(
    r3_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_2'('#skF_5','#skF_6','#skF_6')) ),
    inference(resolution,[status(thm)],[c_25375,c_24961])).

tff(c_25422,plain,
    ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_2'('#skF_5','#skF_6','#skF_6'))
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_25416,c_40])).

tff(c_25425,plain,
    ( r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_2'('#skF_5','#skF_6','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_25375,c_25422])).

tff(c_25426,plain,(
    r1_orders_2('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_2'('#skF_5','#skF_6','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_25425])).

tff(c_25969,plain,(
    ! [E_2043,B_2044,A_2045,C_2046] :
      ( ~ r2_hidden(E_2043,B_2044)
      | ~ r1_orders_2(A_2045,'#skF_2'(A_2045,B_2044,C_2046),E_2043)
      | ~ m1_subset_1(E_2043,u1_struct_0(A_2045))
      | ~ r2_hidden('#skF_2'(A_2045,B_2044,C_2046),C_2046)
      | k3_waybel_0(A_2045,B_2044) = C_2046
      | ~ m1_subset_1(C_2046,k1_zfmisc_1(u1_struct_0(A_2045)))
      | ~ m1_subset_1(B_2044,k1_zfmisc_1(u1_struct_0(A_2045)))
      | ~ l1_orders_2(A_2045) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_25976,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_6')
    | k3_waybel_0('#skF_5','#skF_6') = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_25426,c_25969])).

tff(c_25990,plain,(
    k3_waybel_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_25228,c_25375,c_25976])).

tff(c_25992,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25227,c_25990])).

tff(c_25994,plain,(
    ~ r2_hidden('#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_25226])).

tff(c_25993,plain,(
    r2_hidden('#skF_3'('#skF_5','#skF_6','#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_25226])).

tff(c_24929,plain,(
    ! [A_1865,C_1866,B_1867] :
      ( m1_subset_1(A_1865,C_1866)
      | ~ m1_subset_1(B_1867,k1_zfmisc_1(C_1866))
      | ~ r2_hidden(A_1865,B_1867) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_24932,plain,(
    ! [A_1865] :
      ( m1_subset_1(A_1865,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_1865,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_50,c_24929])).

tff(c_25998,plain,(
    ! [A_2047,C_2048] :
      ( r1_orders_2(A_2047,'#skF_3'('#skF_5','#skF_6','#skF_6'),C_2048)
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6','#skF_6'),u1_struct_0(A_2047))
      | ~ r2_lattice3(A_2047,'#skF_6',C_2048)
      | ~ m1_subset_1(C_2048,u1_struct_0(A_2047))
      | ~ l1_orders_2(A_2047) ) ),
    inference(resolution,[status(thm)],[c_25993,c_28])).

tff(c_26001,plain,(
    ! [C_2048] :
      ( r1_orders_2('#skF_5','#skF_3'('#skF_5','#skF_6','#skF_6'),C_2048)
      | ~ r2_lattice3('#skF_5','#skF_6',C_2048)
      | ~ m1_subset_1(C_2048,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ r2_hidden('#skF_3'('#skF_5','#skF_6','#skF_6'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24932,c_25998])).

tff(c_26011,plain,(
    ! [C_2051] :
      ( r1_orders_2('#skF_5','#skF_3'('#skF_5','#skF_6','#skF_6'),C_2051)
      | ~ r2_lattice3('#skF_5','#skF_6',C_2051)
      | ~ m1_subset_1(C_2051,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25993,c_52,c_26001])).

tff(c_26013,plain,(
    ! [B_113,C_2051] :
      ( r1_orders_2('#skF_5',B_113,C_2051)
      | ~ r1_orders_2('#skF_5',B_113,'#skF_3'('#skF_5','#skF_6','#skF_6'))
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_113,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ r2_lattice3('#skF_5','#skF_6',C_2051)
      | ~ m1_subset_1(C_2051,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_26011,c_44])).

tff(c_26016,plain,(
    ! [B_113,C_2051] :
      ( r1_orders_2('#skF_5',B_113,C_2051)
      | ~ r1_orders_2('#skF_5',B_113,'#skF_3'('#skF_5','#skF_6','#skF_6'))
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_113,u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5','#skF_6',C_2051)
      | ~ m1_subset_1(C_2051,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_26013])).

tff(c_26540,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_26016])).

tff(c_26543,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_6')
    | k3_waybel_0('#skF_5','#skF_6') = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_26540])).

tff(c_26549,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_6')
    | k3_waybel_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_26543])).

tff(c_26551,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25227,c_25994,c_26549])).

tff(c_26553,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_26016])).

tff(c_26092,plain,(
    ! [A_2063,B_2064,C_2065] :
      ( r2_hidden('#skF_2'(A_2063,B_2064,C_2065),C_2065)
      | m1_subset_1('#skF_3'(A_2063,B_2064,C_2065),u1_struct_0(A_2063))
      | k3_waybel_0(A_2063,B_2064) = C_2065
      | ~ m1_subset_1(C_2065,k1_zfmisc_1(u1_struct_0(A_2063)))
      | ~ m1_subset_1(B_2064,k1_zfmisc_1(u1_struct_0(A_2063)))
      | ~ l1_orders_2(A_2063) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26117,plain,(
    ! [B_2064,C_2065] :
      ( r3_orders_2('#skF_5','#skF_3'('#skF_5',B_2064,C_2065),'#skF_3'('#skF_5',B_2064,C_2065))
      | r2_hidden('#skF_2'('#skF_5',B_2064,C_2065),C_2065)
      | k3_waybel_0('#skF_5',B_2064) = C_2065
      | ~ m1_subset_1(C_2065,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_2064,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26092,c_24961])).

tff(c_26527,plain,(
    ! [B_2094,C_2095] :
      ( r3_orders_2('#skF_5','#skF_3'('#skF_5',B_2094,C_2095),'#skF_3'('#skF_5',B_2094,C_2095))
      | r2_hidden('#skF_2'('#skF_5',B_2094,C_2095),C_2095)
      | k3_waybel_0('#skF_5',B_2094) = C_2095
      | ~ m1_subset_1(C_2095,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_2094,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_26117])).

tff(c_26529,plain,(
    ! [B_2094,C_2095] :
      ( r1_orders_2('#skF_5','#skF_3'('#skF_5',B_2094,C_2095),'#skF_3'('#skF_5',B_2094,C_2095))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_2094,C_2095),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | r2_hidden('#skF_2'('#skF_5',B_2094,C_2095),C_2095)
      | k3_waybel_0('#skF_5',B_2094) = C_2095
      | ~ m1_subset_1(C_2095,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_2094,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_26527,c_40])).

tff(c_26532,plain,(
    ! [B_2094,C_2095] :
      ( r1_orders_2('#skF_5','#skF_3'('#skF_5',B_2094,C_2095),'#skF_3'('#skF_5',B_2094,C_2095))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_2094,C_2095),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | r2_hidden('#skF_2'('#skF_5',B_2094,C_2095),C_2095)
      | k3_waybel_0('#skF_5',B_2094) = C_2095
      | ~ m1_subset_1(C_2095,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_2094,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_26529])).

tff(c_26533,plain,(
    ! [B_2094,C_2095] :
      ( r1_orders_2('#skF_5','#skF_3'('#skF_5',B_2094,C_2095),'#skF_3'('#skF_5',B_2094,C_2095))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_2094,C_2095),u1_struct_0('#skF_5'))
      | r2_hidden('#skF_2'('#skF_5',B_2094,C_2095),C_2095)
      | k3_waybel_0('#skF_5',B_2094) = C_2095
      | ~ m1_subset_1(C_2095,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_2094,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_26532])).

tff(c_26882,plain,(
    ! [D_2128,A_2129,B_2130,E_2131] :
      ( r2_hidden(D_2128,k3_waybel_0(A_2129,B_2130))
      | ~ r2_hidden(E_2131,B_2130)
      | ~ r1_orders_2(A_2129,D_2128,E_2131)
      | ~ m1_subset_1(E_2131,u1_struct_0(A_2129))
      | ~ m1_subset_1(D_2128,u1_struct_0(A_2129))
      | ~ m1_subset_1(k3_waybel_0(A_2129,B_2130),k1_zfmisc_1(u1_struct_0(A_2129)))
      | ~ m1_subset_1(B_2130,k1_zfmisc_1(u1_struct_0(A_2129)))
      | ~ l1_orders_2(A_2129) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_27713,plain,(
    ! [D_2234,A_2235] :
      ( r2_hidden(D_2234,k3_waybel_0(A_2235,'#skF_6'))
      | ~ r1_orders_2(A_2235,D_2234,'#skF_3'('#skF_5','#skF_6','#skF_6'))
      | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6','#skF_6'),u1_struct_0(A_2235))
      | ~ m1_subset_1(D_2234,u1_struct_0(A_2235))
      | ~ m1_subset_1(k3_waybel_0(A_2235,'#skF_6'),k1_zfmisc_1(u1_struct_0(A_2235)))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_2235)))
      | ~ l1_orders_2(A_2235) ) ),
    inference(resolution,[status(thm)],[c_25993,c_26882])).

tff(c_27730,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6','#skF_6'),k3_waybel_0('#skF_5','#skF_6'))
    | ~ m1_subset_1(k3_waybel_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_6','#skF_6'),u1_struct_0('#skF_5'))
    | r2_hidden('#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_6')
    | k3_waybel_0('#skF_5','#skF_6') = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_26533,c_27713])).

tff(c_27756,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6','#skF_6'),k3_waybel_0('#skF_5','#skF_6'))
    | ~ m1_subset_1(k3_waybel_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | r2_hidden('#skF_2'('#skF_5','#skF_6','#skF_6'),'#skF_6')
    | k3_waybel_0('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_26553,c_52,c_27730])).

tff(c_27757,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_6','#skF_6'),k3_waybel_0('#skF_5','#skF_6'))
    | ~ m1_subset_1(k3_waybel_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_25227,c_25994,c_27756])).

tff(c_27774,plain,(
    ~ m1_subset_1(k3_waybel_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_27757])).

tff(c_27777,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_27774])).

tff(c_27781,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_27777])).

tff(c_27783,plain,(
    m1_subset_1(k3_waybel_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_27757])).

tff(c_46,plain,(
    ! [A_120,C_122,B_121] :
      ( m1_subset_1(A_120,C_122)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(C_122))
      | ~ r2_hidden(A_120,B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_27844,plain,(
    ! [A_2238] :
      ( m1_subset_1(A_2238,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_2238,k3_waybel_0('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_27783,c_46])).

tff(c_27885,plain,(
    ! [A_85,C_93] :
      ( m1_subset_1('#skF_4'(A_85,k3_waybel_0('#skF_5','#skF_6'),C_93),u1_struct_0('#skF_5'))
      | r2_lattice3(A_85,k3_waybel_0('#skF_5','#skF_6'),C_93)
      | ~ m1_subset_1(C_93,u1_struct_0(A_85))
      | ~ l1_orders_2(A_85) ) ),
    inference(resolution,[status(thm)],[c_32,c_27844])).

tff(c_25171,plain,(
    ! [A_97,B_1930,B_98] :
      ( r2_hidden('#skF_2'(A_97,B_1930,k3_waybel_0(A_97,B_98)),k3_waybel_0(A_97,B_98))
      | r2_hidden('#skF_3'(A_97,B_1930,k3_waybel_0(A_97,B_98)),B_1930)
      | k3_waybel_0(A_97,B_98) = k3_waybel_0(A_97,B_1930)
      | ~ m1_subset_1(B_1930,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_orders_2(A_97) ) ),
    inference(resolution,[status(thm)],[c_36,c_25166])).

tff(c_27855,plain,(
    ! [B_1930] :
      ( m1_subset_1('#skF_2'('#skF_5',B_1930,k3_waybel_0('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
      | r2_hidden('#skF_3'('#skF_5',B_1930,k3_waybel_0('#skF_5','#skF_6')),B_1930)
      | k3_waybel_0('#skF_5',B_1930) = k3_waybel_0('#skF_5','#skF_6')
      | ~ m1_subset_1(B_1930,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_25171,c_27844])).

tff(c_105459,plain,(
    ! [B_5895] :
      ( m1_subset_1('#skF_2'('#skF_5',B_5895,k3_waybel_0('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
      | r2_hidden('#skF_3'('#skF_5',B_5895,k3_waybel_0('#skF_5','#skF_6')),B_5895)
      | k3_waybel_0('#skF_5',B_5895) = k3_waybel_0('#skF_5','#skF_6')
      | ~ m1_subset_1(B_5895,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_27855])).

tff(c_27832,plain,(
    ! [A_120] :
      ( m1_subset_1(A_120,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_120,k3_waybel_0('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_27783,c_46])).

tff(c_105488,plain,
    ( m1_subset_1('#skF_3'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | m1_subset_1('#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | k3_waybel_0('#skF_5',k3_waybel_0('#skF_5','#skF_6')) = k3_waybel_0('#skF_5','#skF_6')
    | ~ m1_subset_1(k3_waybel_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_105459,c_27832])).

tff(c_105536,plain,
    ( m1_subset_1('#skF_3'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | m1_subset_1('#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | k3_waybel_0('#skF_5',k3_waybel_0('#skF_5','#skF_6')) = k3_waybel_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27783,c_105488])).

tff(c_106138,plain,(
    k3_waybel_0('#skF_5',k3_waybel_0('#skF_5','#skF_6')) = k3_waybel_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_105536])).

tff(c_24962,plain,(
    ! [B_1886] :
      ( r3_orders_2('#skF_5',B_1886,B_1886)
      | ~ m1_subset_1(B_1886,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_24960])).

tff(c_24965,plain,(
    ! [B_92,C_93] :
      ( r3_orders_2('#skF_5','#skF_4'('#skF_5',B_92,C_93),'#skF_4'('#skF_5',B_92,C_93))
      | r2_lattice3('#skF_5',B_92,C_93)
      | ~ m1_subset_1(C_93,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_24962])).

tff(c_24972,plain,(
    ! [B_92,C_93] :
      ( r3_orders_2('#skF_5','#skF_4'('#skF_5',B_92,C_93),'#skF_4'('#skF_5',B_92,C_93))
      | r2_lattice3('#skF_5',B_92,C_93)
      | ~ m1_subset_1(C_93,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_24965])).

tff(c_24997,plain,(
    ! [A_1897,B_1898,C_1899] :
      ( r1_orders_2(A_1897,B_1898,C_1899)
      | ~ r3_orders_2(A_1897,B_1898,C_1899)
      | ~ m1_subset_1(C_1899,u1_struct_0(A_1897))
      | ~ m1_subset_1(B_1898,u1_struct_0(A_1897))
      | ~ l1_orders_2(A_1897)
      | ~ v3_orders_2(A_1897)
      | v2_struct_0(A_1897) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24999,plain,(
    ! [B_92,C_93] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_5',B_92,C_93),'#skF_4'('#skF_5',B_92,C_93))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_92,C_93),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | r2_lattice3('#skF_5',B_92,C_93)
      | ~ m1_subset_1(C_93,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_24972,c_24997])).

tff(c_25006,plain,(
    ! [B_92,C_93] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_5',B_92,C_93),'#skF_4'('#skF_5',B_92,C_93))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_92,C_93),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | r2_lattice3('#skF_5',B_92,C_93)
      | ~ m1_subset_1(C_93,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_24999])).

tff(c_25007,plain,(
    ! [B_92,C_93] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_5',B_92,C_93),'#skF_4'('#skF_5',B_92,C_93))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_92,C_93),u1_struct_0('#skF_5'))
      | r2_lattice3('#skF_5',B_92,C_93)
      | ~ m1_subset_1(C_93,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_25006])).

tff(c_34597,plain,(
    ! [A_2591,C_2589,D_2587,B_2588,A_2590] :
      ( r2_hidden(D_2587,k3_waybel_0(A_2590,B_2588))
      | ~ r1_orders_2(A_2590,D_2587,'#skF_4'(A_2591,B_2588,C_2589))
      | ~ m1_subset_1('#skF_4'(A_2591,B_2588,C_2589),u1_struct_0(A_2590))
      | ~ m1_subset_1(D_2587,u1_struct_0(A_2590))
      | ~ m1_subset_1(k3_waybel_0(A_2590,B_2588),k1_zfmisc_1(u1_struct_0(A_2590)))
      | ~ m1_subset_1(B_2588,k1_zfmisc_1(u1_struct_0(A_2590)))
      | ~ l1_orders_2(A_2590)
      | r2_lattice3(A_2591,B_2588,C_2589)
      | ~ m1_subset_1(C_2589,u1_struct_0(A_2591))
      | ~ l1_orders_2(A_2591) ) ),
    inference(resolution,[status(thm)],[c_32,c_26882])).

tff(c_34613,plain,(
    ! [B_92,C_93] :
      ( r2_hidden('#skF_4'('#skF_5',B_92,C_93),k3_waybel_0('#skF_5',B_92))
      | ~ m1_subset_1(k3_waybel_0('#skF_5',B_92),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ m1_subset_1('#skF_4'('#skF_5',B_92,C_93),u1_struct_0('#skF_5'))
      | r2_lattice3('#skF_5',B_92,C_93)
      | ~ m1_subset_1(C_93,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_25007,c_34597])).

tff(c_107210,plain,(
    ! [B_5980,C_5981] :
      ( r2_hidden('#skF_4'('#skF_5',B_5980,C_5981),k3_waybel_0('#skF_5',B_5980))
      | ~ m1_subset_1(k3_waybel_0('#skF_5',B_5980),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_5980,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_5980,C_5981),u1_struct_0('#skF_5'))
      | r2_lattice3('#skF_5',B_5980,C_5981)
      | ~ m1_subset_1(C_5981,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_34613])).

tff(c_107212,plain,(
    ! [C_5981] :
      ( r2_hidden('#skF_4'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),C_5981),k3_waybel_0('#skF_5',k3_waybel_0('#skF_5','#skF_6')))
      | ~ m1_subset_1(k3_waybel_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(k3_waybel_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_4'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),C_5981),u1_struct_0('#skF_5'))
      | r2_lattice3('#skF_5',k3_waybel_0('#skF_5','#skF_6'),C_5981)
      | ~ m1_subset_1(C_5981,u1_struct_0('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106138,c_107210])).

tff(c_107219,plain,(
    ! [C_5981] :
      ( r2_hidden('#skF_4'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),C_5981),k3_waybel_0('#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_4'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),C_5981),u1_struct_0('#skF_5'))
      | r2_lattice3('#skF_5',k3_waybel_0('#skF_5','#skF_6'),C_5981)
      | ~ m1_subset_1(C_5981,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27783,c_27783,c_106138,c_107212])).

tff(c_26,plain,(
    ! [A_1,B_45,D_78] :
      ( m1_subset_1('#skF_1'(A_1,B_45,k3_waybel_0(A_1,B_45),D_78),u1_struct_0(A_1))
      | ~ r2_hidden(D_78,k3_waybel_0(A_1,B_45))
      | ~ m1_subset_1(D_78,u1_struct_0(A_1))
      | ~ m1_subset_1(k3_waybel_0(A_1,B_45),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26604,plain,(
    ! [A_2098,D_2099,B_2100] :
      ( r1_orders_2(A_2098,D_2099,'#skF_1'(A_2098,B_2100,k3_waybel_0(A_2098,B_2100),D_2099))
      | ~ r2_hidden(D_2099,k3_waybel_0(A_2098,B_2100))
      | ~ m1_subset_1(D_2099,u1_struct_0(A_2098))
      | ~ m1_subset_1(k3_waybel_0(A_2098,B_2100),k1_zfmisc_1(u1_struct_0(A_2098)))
      | ~ m1_subset_1(B_2100,k1_zfmisc_1(u1_struct_0(A_2098)))
      | ~ l1_orders_2(A_2098) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26607,plain,(
    ! [A_97,D_2099,B_98] :
      ( r1_orders_2(A_97,D_2099,'#skF_1'(A_97,B_98,k3_waybel_0(A_97,B_98),D_2099))
      | ~ r2_hidden(D_2099,k3_waybel_0(A_97,B_98))
      | ~ m1_subset_1(D_2099,u1_struct_0(A_97))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_orders_2(A_97) ) ),
    inference(resolution,[status(thm)],[c_36,c_26604])).

tff(c_26414,plain,(
    ! [A_2079,B_2080,D_2081] :
      ( r2_hidden('#skF_1'(A_2079,B_2080,k3_waybel_0(A_2079,B_2080),D_2081),B_2080)
      | ~ r2_hidden(D_2081,k3_waybel_0(A_2079,B_2080))
      | ~ m1_subset_1(D_2081,u1_struct_0(A_2079))
      | ~ m1_subset_1(k3_waybel_0(A_2079,B_2080),k1_zfmisc_1(u1_struct_0(A_2079)))
      | ~ m1_subset_1(B_2080,k1_zfmisc_1(u1_struct_0(A_2079)))
      | ~ l1_orders_2(A_2079) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26464,plain,(
    ! [A_2085,B_2086,D_2087] :
      ( r2_hidden('#skF_1'(A_2085,B_2086,k3_waybel_0(A_2085,B_2086),D_2087),B_2086)
      | ~ r2_hidden(D_2087,k3_waybel_0(A_2085,B_2086))
      | ~ m1_subset_1(D_2087,u1_struct_0(A_2085))
      | ~ m1_subset_1(B_2086,k1_zfmisc_1(u1_struct_0(A_2085)))
      | ~ l1_orders_2(A_2085) ) ),
    inference(resolution,[status(thm)],[c_36,c_26414])).

tff(c_107949,plain,(
    ! [D_6037,A_6038,A_6040,C_6039,B_6036] :
      ( r1_orders_2(A_6040,'#skF_1'(A_6038,B_6036,k3_waybel_0(A_6038,B_6036),D_6037),C_6039)
      | ~ m1_subset_1('#skF_1'(A_6038,B_6036,k3_waybel_0(A_6038,B_6036),D_6037),u1_struct_0(A_6040))
      | ~ r2_lattice3(A_6040,B_6036,C_6039)
      | ~ m1_subset_1(C_6039,u1_struct_0(A_6040))
      | ~ l1_orders_2(A_6040)
      | ~ r2_hidden(D_6037,k3_waybel_0(A_6038,B_6036))
      | ~ m1_subset_1(D_6037,u1_struct_0(A_6038))
      | ~ m1_subset_1(B_6036,k1_zfmisc_1(u1_struct_0(A_6038)))
      | ~ l1_orders_2(A_6038) ) ),
    inference(resolution,[status(thm)],[c_26464,c_28])).

tff(c_110032,plain,(
    ! [A_6174,B_6175,D_6176,C_6177] :
      ( r1_orders_2(A_6174,'#skF_1'(A_6174,B_6175,k3_waybel_0(A_6174,B_6175),D_6176),C_6177)
      | ~ r2_lattice3(A_6174,B_6175,C_6177)
      | ~ m1_subset_1(C_6177,u1_struct_0(A_6174))
      | ~ r2_hidden(D_6176,k3_waybel_0(A_6174,B_6175))
      | ~ m1_subset_1(D_6176,u1_struct_0(A_6174))
      | ~ m1_subset_1(k3_waybel_0(A_6174,B_6175),k1_zfmisc_1(u1_struct_0(A_6174)))
      | ~ m1_subset_1(B_6175,k1_zfmisc_1(u1_struct_0(A_6174)))
      | ~ l1_orders_2(A_6174) ) ),
    inference(resolution,[status(thm)],[c_26,c_107949])).

tff(c_110036,plain,(
    ! [D_6176,C_6177] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5','#skF_6',k3_waybel_0('#skF_5','#skF_6'),D_6176),C_6177)
      | ~ r2_lattice3('#skF_5','#skF_6',C_6177)
      | ~ m1_subset_1(C_6177,u1_struct_0('#skF_5'))
      | ~ r2_hidden(D_6176,k3_waybel_0('#skF_5','#skF_6'))
      | ~ m1_subset_1(D_6176,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_27783,c_110032])).

tff(c_110088,plain,(
    ! [D_6183,C_6184] :
      ( r1_orders_2('#skF_5','#skF_1'('#skF_5','#skF_6',k3_waybel_0('#skF_5','#skF_6'),D_6183),C_6184)
      | ~ r2_lattice3('#skF_5','#skF_6',C_6184)
      | ~ m1_subset_1(C_6184,u1_struct_0('#skF_5'))
      | ~ r2_hidden(D_6183,k3_waybel_0('#skF_5','#skF_6'))
      | ~ m1_subset_1(D_6183,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_110036])).

tff(c_110141,plain,(
    ! [B_113,C_6184,D_6183] :
      ( r1_orders_2('#skF_5',B_113,C_6184)
      | ~ r1_orders_2('#skF_5',B_113,'#skF_1'('#skF_5','#skF_6',k3_waybel_0('#skF_5','#skF_6'),D_6183))
      | ~ m1_subset_1('#skF_1'('#skF_5','#skF_6',k3_waybel_0('#skF_5','#skF_6'),D_6183),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_113,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ r2_lattice3('#skF_5','#skF_6',C_6184)
      | ~ m1_subset_1(C_6184,u1_struct_0('#skF_5'))
      | ~ r2_hidden(D_6183,k3_waybel_0('#skF_5','#skF_6'))
      | ~ m1_subset_1(D_6183,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_110088,c_44])).

tff(c_139111,plain,(
    ! [B_7242,C_7243,D_7244] :
      ( r1_orders_2('#skF_5',B_7242,C_7243)
      | ~ r1_orders_2('#skF_5',B_7242,'#skF_1'('#skF_5','#skF_6',k3_waybel_0('#skF_5','#skF_6'),D_7244))
      | ~ m1_subset_1('#skF_1'('#skF_5','#skF_6',k3_waybel_0('#skF_5','#skF_6'),D_7244),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_7242,u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5','#skF_6',C_7243)
      | ~ m1_subset_1(C_7243,u1_struct_0('#skF_5'))
      | ~ r2_hidden(D_7244,k3_waybel_0('#skF_5','#skF_6'))
      | ~ m1_subset_1(D_7244,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_110141])).

tff(c_139232,plain,(
    ! [D_2099,C_7243] :
      ( r1_orders_2('#skF_5',D_2099,C_7243)
      | ~ m1_subset_1('#skF_1'('#skF_5','#skF_6',k3_waybel_0('#skF_5','#skF_6'),D_2099),u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5','#skF_6',C_7243)
      | ~ m1_subset_1(C_7243,u1_struct_0('#skF_5'))
      | ~ r2_hidden(D_2099,k3_waybel_0('#skF_5','#skF_6'))
      | ~ m1_subset_1(D_2099,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26607,c_139111])).

tff(c_139525,plain,(
    ! [D_7250,C_7251] :
      ( r1_orders_2('#skF_5',D_7250,C_7251)
      | ~ m1_subset_1('#skF_1'('#skF_5','#skF_6',k3_waybel_0('#skF_5','#skF_6'),D_7250),u1_struct_0('#skF_5'))
      | ~ r2_lattice3('#skF_5','#skF_6',C_7251)
      | ~ m1_subset_1(C_7251,u1_struct_0('#skF_5'))
      | ~ r2_hidden(D_7250,k3_waybel_0('#skF_5','#skF_6'))
      | ~ m1_subset_1(D_7250,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_139232])).

tff(c_139528,plain,(
    ! [D_78,C_7251] :
      ( r1_orders_2('#skF_5',D_78,C_7251)
      | ~ r2_lattice3('#skF_5','#skF_6',C_7251)
      | ~ m1_subset_1(C_7251,u1_struct_0('#skF_5'))
      | ~ r2_hidden(D_78,k3_waybel_0('#skF_5','#skF_6'))
      | ~ m1_subset_1(D_78,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k3_waybel_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26,c_139525])).

tff(c_139536,plain,(
    ! [D_7252,C_7253] :
      ( r1_orders_2('#skF_5',D_7252,C_7253)
      | ~ r2_lattice3('#skF_5','#skF_6',C_7253)
      | ~ m1_subset_1(C_7253,u1_struct_0('#skF_5'))
      | ~ r2_hidden(D_7252,k3_waybel_0('#skF_5','#skF_6'))
      | ~ m1_subset_1(D_7252,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_27783,c_139528])).

tff(c_139674,plain,(
    ! [D_7252] :
      ( r1_orders_2('#skF_5',D_7252,'#skF_7')
      | ~ r2_lattice3('#skF_5','#skF_6','#skF_7')
      | ~ r2_hidden(D_7252,k3_waybel_0('#skF_5','#skF_6'))
      | ~ m1_subset_1(D_7252,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_48,c_139536])).

tff(c_139771,plain,(
    ! [D_7254] :
      ( r1_orders_2('#skF_5',D_7254,'#skF_7')
      | ~ r2_hidden(D_7254,k3_waybel_0('#skF_5','#skF_6'))
      | ~ m1_subset_1(D_7254,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24925,c_139674])).

tff(c_140054,plain,(
    ! [C_7257] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),C_7257),'#skF_7')
      | ~ m1_subset_1('#skF_4'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),C_7257),u1_struct_0('#skF_5'))
      | r2_lattice3('#skF_5',k3_waybel_0('#skF_5','#skF_6'),C_7257)
      | ~ m1_subset_1(C_7257,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_107219,c_139771])).

tff(c_140058,plain,(
    ! [C_93] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),C_93),'#skF_7')
      | r2_lattice3('#skF_5',k3_waybel_0('#skF_5','#skF_6'),C_93)
      | ~ m1_subset_1(C_93,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_27885,c_140054])).

tff(c_140096,plain,(
    ! [C_7263] :
      ( r1_orders_2('#skF_5','#skF_4'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),C_7263),'#skF_7')
      | r2_lattice3('#skF_5',k3_waybel_0('#skF_5','#skF_6'),C_7263)
      | ~ m1_subset_1(C_7263,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_140058])).

tff(c_140114,plain,
    ( ~ l1_orders_2('#skF_5')
    | r2_lattice3('#skF_5',k3_waybel_0('#skF_5','#skF_6'),'#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_140096,c_30])).

tff(c_140138,plain,(
    r2_lattice3('#skF_5',k3_waybel_0('#skF_5','#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52,c_140114])).

tff(c_140140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24926,c_140138])).

tff(c_140142,plain,(
    k3_waybel_0('#skF_5',k3_waybel_0('#skF_5','#skF_6')) != k3_waybel_0('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_105536])).

tff(c_25113,plain,(
    ! [B_1914,C_1915] :
      ( r3_orders_2('#skF_5','#skF_2'('#skF_5',B_1914,C_1915),'#skF_2'('#skF_5',B_1914,C_1915))
      | k3_waybel_0('#skF_5',B_1914) = C_1915
      | ~ m1_subset_1(C_1915,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1914,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_25099,c_24961])).

tff(c_25135,plain,(
    ! [B_1918,C_1919] :
      ( r3_orders_2('#skF_5','#skF_2'('#skF_5',B_1918,C_1919),'#skF_2'('#skF_5',B_1918,C_1919))
      | k3_waybel_0('#skF_5',B_1918) = C_1919
      | ~ m1_subset_1(C_1919,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1918,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_25113])).

tff(c_25137,plain,(
    ! [B_1918,C_1919] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5',B_1918,C_1919),'#skF_2'('#skF_5',B_1918,C_1919))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_1918,C_1919),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | k3_waybel_0('#skF_5',B_1918) = C_1919
      | ~ m1_subset_1(C_1919,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1918,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_25135,c_40])).

tff(c_25140,plain,(
    ! [B_1918,C_1919] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5',B_1918,C_1919),'#skF_2'('#skF_5',B_1918,C_1919))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_1918,C_1919),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | k3_waybel_0('#skF_5',B_1918) = C_1919
      | ~ m1_subset_1(C_1919,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1918,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_25137])).

tff(c_25141,plain,(
    ! [B_1918,C_1919] :
      ( r1_orders_2('#skF_5','#skF_2'('#skF_5',B_1918,C_1919),'#skF_2'('#skF_5',B_1918,C_1919))
      | ~ m1_subset_1('#skF_2'('#skF_5',B_1918,C_1919),u1_struct_0('#skF_5'))
      | k3_waybel_0('#skF_5',B_1918) = C_1919
      | ~ m1_subset_1(C_1919,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1918,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_25140])).

tff(c_27036,plain,(
    ! [E_2160,B_2161,A_2162,C_2163] :
      ( ~ r2_hidden(E_2160,B_2161)
      | ~ r1_orders_2(A_2162,'#skF_2'(A_2162,B_2161,C_2163),E_2160)
      | ~ m1_subset_1(E_2160,u1_struct_0(A_2162))
      | ~ r2_hidden('#skF_2'(A_2162,B_2161,C_2163),C_2163)
      | k3_waybel_0(A_2162,B_2161) = C_2163
      | ~ m1_subset_1(C_2163,k1_zfmisc_1(u1_struct_0(A_2162)))
      | ~ m1_subset_1(B_2161,k1_zfmisc_1(u1_struct_0(A_2162)))
      | ~ l1_orders_2(A_2162) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_27049,plain,(
    ! [B_1918,C_1919] :
      ( ~ r2_hidden('#skF_2'('#skF_5',B_1918,C_1919),B_1918)
      | ~ r2_hidden('#skF_2'('#skF_5',B_1918,C_1919),C_1919)
      | ~ l1_orders_2('#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_5',B_1918,C_1919),u1_struct_0('#skF_5'))
      | k3_waybel_0('#skF_5',B_1918) = C_1919
      | ~ m1_subset_1(C_1919,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1918,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_25141,c_27036])).

tff(c_27132,plain,(
    ! [B_2172,C_2173] :
      ( ~ r2_hidden('#skF_2'('#skF_5',B_2172,C_2173),B_2172)
      | ~ r2_hidden('#skF_2'('#skF_5',B_2172,C_2173),C_2173)
      | ~ m1_subset_1('#skF_2'('#skF_5',B_2172,C_2173),u1_struct_0('#skF_5'))
      | k3_waybel_0('#skF_5',B_2172) = C_2173
      | ~ m1_subset_1(C_2173,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_2172,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_27049])).

tff(c_27135,plain,(
    ! [C_67] :
      ( ~ r2_hidden('#skF_2'('#skF_5',C_67,C_67),C_67)
      | ~ m1_subset_1('#skF_2'('#skF_5',C_67,C_67),u1_struct_0('#skF_5'))
      | m1_subset_1('#skF_3'('#skF_5',C_67,C_67),u1_struct_0('#skF_5'))
      | k3_waybel_0('#skF_5',C_67) = C_67
      | ~ m1_subset_1(C_67,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_18,c_27132])).

tff(c_27139,plain,(
    ! [C_2174] :
      ( ~ r2_hidden('#skF_2'('#skF_5',C_2174,C_2174),C_2174)
      | ~ m1_subset_1('#skF_2'('#skF_5',C_2174,C_2174),u1_struct_0('#skF_5'))
      | m1_subset_1('#skF_3'('#skF_5',C_2174,C_2174),u1_struct_0('#skF_5'))
      | k3_waybel_0('#skF_5',C_2174) = C_2174
      | ~ m1_subset_1(C_2174,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_27135])).

tff(c_27142,plain,(
    ! [C_67] :
      ( ~ m1_subset_1('#skF_2'('#skF_5',C_67,C_67),u1_struct_0('#skF_5'))
      | m1_subset_1('#skF_3'('#skF_5',C_67,C_67),u1_struct_0('#skF_5'))
      | k3_waybel_0('#skF_5',C_67) = C_67
      | ~ m1_subset_1(C_67,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_18,c_27139])).

tff(c_27146,plain,(
    ! [C_2175] :
      ( ~ m1_subset_1('#skF_2'('#skF_5',C_2175,C_2175),u1_struct_0('#skF_5'))
      | m1_subset_1('#skF_3'('#skF_5',C_2175,C_2175),u1_struct_0('#skF_5'))
      | k3_waybel_0('#skF_5',C_2175) = C_2175
      | ~ m1_subset_1(C_2175,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_27142])).

tff(c_27153,plain,(
    ! [C_67] :
      ( m1_subset_1('#skF_3'('#skF_5',C_67,C_67),u1_struct_0('#skF_5'))
      | k3_waybel_0('#skF_5',C_67) = C_67
      | ~ m1_subset_1(C_67,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2,c_27146])).

tff(c_27163,plain,(
    ! [C_67] :
      ( m1_subset_1('#skF_3'('#skF_5',C_67,C_67),u1_struct_0('#skF_5'))
      | k3_waybel_0('#skF_5',C_67) = C_67
      | ~ m1_subset_1(C_67,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_27153])).

tff(c_10,plain,(
    ! [A_1,B_45,C_67] :
      ( r2_hidden('#skF_2'(A_1,B_45,C_67),C_67)
      | r2_hidden('#skF_3'(A_1,B_45,C_67),B_45)
      | k3_waybel_0(A_1,B_45) = C_67
      | ~ m1_subset_1(C_67,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_27811,plain,(
    ! [B_45] :
      ( r2_hidden('#skF_2'('#skF_5',B_45,k3_waybel_0('#skF_5','#skF_6')),k3_waybel_0('#skF_5','#skF_6'))
      | r2_hidden('#skF_3'('#skF_5',B_45,k3_waybel_0('#skF_5','#skF_6')),B_45)
      | k3_waybel_0('#skF_5',B_45) = k3_waybel_0('#skF_5','#skF_6')
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_27783,c_10])).

tff(c_105547,plain,(
    ! [B_5897] :
      ( r2_hidden('#skF_2'('#skF_5',B_5897,k3_waybel_0('#skF_5','#skF_6')),k3_waybel_0('#skF_5','#skF_6'))
      | r2_hidden('#skF_3'('#skF_5',B_5897,k3_waybel_0('#skF_5','#skF_6')),B_5897)
      | k3_waybel_0('#skF_5',B_5897) = k3_waybel_0('#skF_5','#skF_6')
      | ~ m1_subset_1(B_5897,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_27811])).

tff(c_27165,plain,(
    ! [E_2176,B_2177,A_2178,C_2179] :
      ( ~ r2_hidden(E_2176,B_2177)
      | ~ r1_orders_2(A_2178,'#skF_2'(A_2178,B_2177,C_2179),E_2176)
      | ~ m1_subset_1(E_2176,u1_struct_0(A_2178))
      | r2_hidden('#skF_3'(A_2178,B_2177,C_2179),B_2177)
      | k3_waybel_0(A_2178,B_2177) = C_2179
      | ~ m1_subset_1(C_2179,k1_zfmisc_1(u1_struct_0(A_2178)))
      | ~ m1_subset_1(B_2177,k1_zfmisc_1(u1_struct_0(A_2178)))
      | ~ l1_orders_2(A_2178) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_27178,plain,(
    ! [B_1918,C_1919] :
      ( ~ r2_hidden('#skF_2'('#skF_5',B_1918,C_1919),B_1918)
      | r2_hidden('#skF_3'('#skF_5',B_1918,C_1919),B_1918)
      | ~ l1_orders_2('#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_5',B_1918,C_1919),u1_struct_0('#skF_5'))
      | k3_waybel_0('#skF_5',B_1918) = C_1919
      | ~ m1_subset_1(C_1919,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1918,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_25141,c_27165])).

tff(c_27198,plain,(
    ! [B_1918,C_1919] :
      ( ~ r2_hidden('#skF_2'('#skF_5',B_1918,C_1919),B_1918)
      | r2_hidden('#skF_3'('#skF_5',B_1918,C_1919),B_1918)
      | ~ m1_subset_1('#skF_2'('#skF_5',B_1918,C_1919),u1_struct_0('#skF_5'))
      | k3_waybel_0('#skF_5',B_1918) = C_1919
      | ~ m1_subset_1(C_1919,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_1918,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_27178])).

tff(c_105556,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | r2_hidden('#skF_3'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),k3_waybel_0('#skF_5','#skF_6'))
    | k3_waybel_0('#skF_5',k3_waybel_0('#skF_5','#skF_6')) = k3_waybel_0('#skF_5','#skF_6')
    | ~ m1_subset_1(k3_waybel_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_105547,c_27198])).

tff(c_105581,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | r2_hidden('#skF_3'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),k3_waybel_0('#skF_5','#skF_6'))
    | k3_waybel_0('#skF_5',k3_waybel_0('#skF_5','#skF_6')) = k3_waybel_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27783,c_105556])).

tff(c_140282,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | r2_hidden('#skF_3'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),k3_waybel_0('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_140142,c_105581])).

tff(c_140283,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_140282])).

tff(c_140288,plain,
    ( k3_waybel_0('#skF_5',k3_waybel_0('#skF_5','#skF_6')) = k3_waybel_0('#skF_5','#skF_6')
    | ~ m1_subset_1(k3_waybel_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_140283])).

tff(c_140294,plain,(
    k3_waybel_0('#skF_5',k3_waybel_0('#skF_5','#skF_6')) = k3_waybel_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_27783,c_140288])).

tff(c_140296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_140142,c_140294])).

tff(c_140298,plain,(
    m1_subset_1('#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_140282])).

tff(c_140358,plain,(
    r3_orders_2('#skF_5','#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),'#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_140298,c_24961])).

tff(c_140564,plain,
    ( r1_orders_2('#skF_5','#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),'#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')))
    | ~ m1_subset_1('#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_140358,c_40])).

tff(c_140567,plain,
    ( r1_orders_2('#skF_5','#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),'#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_140298,c_140564])).

tff(c_140568,plain,(
    r1_orders_2('#skF_5','#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),'#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_140567])).

tff(c_4,plain,(
    ! [E_84,B_45,A_1,C_67] :
      ( ~ r2_hidden(E_84,B_45)
      | ~ r1_orders_2(A_1,'#skF_2'(A_1,B_45,C_67),E_84)
      | ~ m1_subset_1(E_84,u1_struct_0(A_1))
      | ~ r2_hidden('#skF_2'(A_1,B_45,C_67),C_67)
      | k3_waybel_0(A_1,B_45) = C_67
      | ~ m1_subset_1(C_67,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_140580,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),k3_waybel_0('#skF_5','#skF_6'))
    | k3_waybel_0('#skF_5',k3_waybel_0('#skF_5','#skF_6')) = k3_waybel_0('#skF_5','#skF_6')
    | ~ m1_subset_1(k3_waybel_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_140568,c_4])).

tff(c_140605,plain,
    ( ~ r2_hidden('#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),k3_waybel_0('#skF_5','#skF_6'))
    | k3_waybel_0('#skF_5',k3_waybel_0('#skF_5','#skF_6')) = k3_waybel_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_27783,c_140298,c_140580])).

tff(c_140606,plain,(
    ~ r2_hidden('#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),k3_waybel_0('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_140142,c_140605])).

tff(c_140141,plain,
    ( m1_subset_1('#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | m1_subset_1('#skF_3'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_105536])).

tff(c_140143,plain,(
    m1_subset_1('#skF_3'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_140141])).

tff(c_140297,plain,(
    r2_hidden('#skF_3'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),k3_waybel_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_140282])).

tff(c_26481,plain,(
    ! [A_2089,B_2090,C_2091] :
      ( r2_hidden('#skF_2'(A_2089,B_2090,C_2091),C_2091)
      | r1_orders_2(A_2089,'#skF_2'(A_2089,B_2090,C_2091),'#skF_3'(A_2089,B_2090,C_2091))
      | k3_waybel_0(A_2089,B_2090) = C_2091
      | ~ m1_subset_1(C_2091,k1_zfmisc_1(u1_struct_0(A_2089)))
      | ~ m1_subset_1(B_2090,k1_zfmisc_1(u1_struct_0(A_2089)))
      | ~ l1_orders_2(A_2089) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26484,plain,(
    ! [A_2089,B_113,B_2090,C_2091] :
      ( r1_orders_2(A_2089,B_113,'#skF_3'(A_2089,B_2090,C_2091))
      | ~ r1_orders_2(A_2089,B_113,'#skF_2'(A_2089,B_2090,C_2091))
      | ~ m1_subset_1('#skF_3'(A_2089,B_2090,C_2091),u1_struct_0(A_2089))
      | ~ m1_subset_1('#skF_2'(A_2089,B_2090,C_2091),u1_struct_0(A_2089))
      | ~ m1_subset_1(B_113,u1_struct_0(A_2089))
      | ~ v4_orders_2(A_2089)
      | r2_hidden('#skF_2'(A_2089,B_2090,C_2091),C_2091)
      | k3_waybel_0(A_2089,B_2090) = C_2091
      | ~ m1_subset_1(C_2091,k1_zfmisc_1(u1_struct_0(A_2089)))
      | ~ m1_subset_1(B_2090,k1_zfmisc_1(u1_struct_0(A_2089)))
      | ~ l1_orders_2(A_2089) ) ),
    inference(resolution,[status(thm)],[c_26481,c_44])).

tff(c_140572,plain,
    ( r1_orders_2('#skF_5','#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),'#skF_3'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')))
    | ~ m1_subset_1('#skF_3'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | ~ v4_orders_2('#skF_5')
    | r2_hidden('#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),k3_waybel_0('#skF_5','#skF_6'))
    | k3_waybel_0('#skF_5',k3_waybel_0('#skF_5','#skF_6')) = k3_waybel_0('#skF_5','#skF_6')
    | ~ m1_subset_1(k3_waybel_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_140568,c_26484])).

tff(c_140589,plain,
    ( r1_orders_2('#skF_5','#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),'#skF_3'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')))
    | r2_hidden('#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),k3_waybel_0('#skF_5','#skF_6'))
    | k3_waybel_0('#skF_5',k3_waybel_0('#skF_5','#skF_6')) = k3_waybel_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_27783,c_54,c_140298,c_140143,c_140572])).

tff(c_140590,plain,
    ( r1_orders_2('#skF_5','#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),'#skF_3'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')))
    | r2_hidden('#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),k3_waybel_0('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_140142,c_140589])).

tff(c_140749,plain,(
    r1_orders_2('#skF_5','#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),'#skF_3'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_140606,c_140590])).

tff(c_26804,plain,(
    ! [A_2112,D_2113,B_2114] :
      ( r1_orders_2(A_2112,D_2113,'#skF_1'(A_2112,B_2114,k3_waybel_0(A_2112,B_2114),D_2113))
      | ~ r2_hidden(D_2113,k3_waybel_0(A_2112,B_2114))
      | ~ m1_subset_1(D_2113,u1_struct_0(A_2112))
      | ~ m1_subset_1(B_2114,k1_zfmisc_1(u1_struct_0(A_2112)))
      | ~ l1_orders_2(A_2112) ) ),
    inference(resolution,[status(thm)],[c_36,c_26604])).

tff(c_141975,plain,(
    ! [A_7355,B_7356,B_7357,D_7358] :
      ( r1_orders_2(A_7355,B_7356,'#skF_1'(A_7355,B_7357,k3_waybel_0(A_7355,B_7357),D_7358))
      | ~ r1_orders_2(A_7355,B_7356,D_7358)
      | ~ m1_subset_1('#skF_1'(A_7355,B_7357,k3_waybel_0(A_7355,B_7357),D_7358),u1_struct_0(A_7355))
      | ~ m1_subset_1(B_7356,u1_struct_0(A_7355))
      | ~ v4_orders_2(A_7355)
      | ~ r2_hidden(D_7358,k3_waybel_0(A_7355,B_7357))
      | ~ m1_subset_1(D_7358,u1_struct_0(A_7355))
      | ~ m1_subset_1(B_7357,k1_zfmisc_1(u1_struct_0(A_7355)))
      | ~ l1_orders_2(A_7355) ) ),
    inference(resolution,[status(thm)],[c_26804,c_44])).

tff(c_150050,plain,(
    ! [A_7743,B_7744,B_7745,D_7746] :
      ( r1_orders_2(A_7743,B_7744,'#skF_1'(A_7743,B_7745,k3_waybel_0(A_7743,B_7745),D_7746))
      | ~ r1_orders_2(A_7743,B_7744,D_7746)
      | ~ m1_subset_1(B_7744,u1_struct_0(A_7743))
      | ~ v4_orders_2(A_7743)
      | ~ r2_hidden(D_7746,k3_waybel_0(A_7743,B_7745))
      | ~ m1_subset_1(D_7746,u1_struct_0(A_7743))
      | ~ m1_subset_1(k3_waybel_0(A_7743,B_7745),k1_zfmisc_1(u1_struct_0(A_7743)))
      | ~ m1_subset_1(B_7745,k1_zfmisc_1(u1_struct_0(A_7743)))
      | ~ l1_orders_2(A_7743) ) ),
    inference(resolution,[status(thm)],[c_26,c_141975])).

tff(c_150054,plain,(
    ! [B_7744,D_7746] :
      ( r1_orders_2('#skF_5',B_7744,'#skF_1'('#skF_5','#skF_6',k3_waybel_0('#skF_5','#skF_6'),D_7746))
      | ~ r1_orders_2('#skF_5',B_7744,D_7746)
      | ~ m1_subset_1(B_7744,u1_struct_0('#skF_5'))
      | ~ v4_orders_2('#skF_5')
      | ~ r2_hidden(D_7746,k3_waybel_0('#skF_5','#skF_6'))
      | ~ m1_subset_1(D_7746,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_27783,c_150050])).

tff(c_150064,plain,(
    ! [B_7747,D_7748] :
      ( r1_orders_2('#skF_5',B_7747,'#skF_1'('#skF_5','#skF_6',k3_waybel_0('#skF_5','#skF_6'),D_7748))
      | ~ r1_orders_2('#skF_5',B_7747,D_7748)
      | ~ m1_subset_1(B_7747,u1_struct_0('#skF_5'))
      | ~ r2_hidden(D_7748,k3_waybel_0('#skF_5','#skF_6'))
      | ~ m1_subset_1(D_7748,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_54,c_150054])).

tff(c_26417,plain,(
    ! [A_97,B_98,D_2081] :
      ( r2_hidden('#skF_1'(A_97,B_98,k3_waybel_0(A_97,B_98),D_2081),B_98)
      | ~ r2_hidden(D_2081,k3_waybel_0(A_97,B_98))
      | ~ m1_subset_1(D_2081,u1_struct_0(A_97))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_orders_2(A_97) ) ),
    inference(resolution,[status(thm)],[c_36,c_26414])).

tff(c_26894,plain,(
    ! [D_2128,B_98,D_2081,A_97,A_2129] :
      ( r2_hidden(D_2128,k3_waybel_0(A_2129,B_98))
      | ~ r1_orders_2(A_2129,D_2128,'#skF_1'(A_97,B_98,k3_waybel_0(A_97,B_98),D_2081))
      | ~ m1_subset_1('#skF_1'(A_97,B_98,k3_waybel_0(A_97,B_98),D_2081),u1_struct_0(A_2129))
      | ~ m1_subset_1(D_2128,u1_struct_0(A_2129))
      | ~ m1_subset_1(k3_waybel_0(A_2129,B_98),k1_zfmisc_1(u1_struct_0(A_2129)))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_2129)))
      | ~ l1_orders_2(A_2129)
      | ~ r2_hidden(D_2081,k3_waybel_0(A_97,B_98))
      | ~ m1_subset_1(D_2081,u1_struct_0(A_97))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_orders_2(A_97) ) ),
    inference(resolution,[status(thm)],[c_26417,c_26882])).

tff(c_150066,plain,(
    ! [B_7747,D_7748] :
      ( r2_hidden(B_7747,k3_waybel_0('#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_1'('#skF_5','#skF_6',k3_waybel_0('#skF_5','#skF_6'),D_7748),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k3_waybel_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ r1_orders_2('#skF_5',B_7747,D_7748)
      | ~ m1_subset_1(B_7747,u1_struct_0('#skF_5'))
      | ~ r2_hidden(D_7748,k3_waybel_0('#skF_5','#skF_6'))
      | ~ m1_subset_1(D_7748,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_150064,c_26894])).

tff(c_150106,plain,(
    ! [B_7749,D_7750] :
      ( r2_hidden(B_7749,k3_waybel_0('#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_1'('#skF_5','#skF_6',k3_waybel_0('#skF_5','#skF_6'),D_7750),u1_struct_0('#skF_5'))
      | ~ r1_orders_2('#skF_5',B_7749,D_7750)
      | ~ m1_subset_1(B_7749,u1_struct_0('#skF_5'))
      | ~ r2_hidden(D_7750,k3_waybel_0('#skF_5','#skF_6'))
      | ~ m1_subset_1(D_7750,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_27783,c_150066])).

tff(c_150109,plain,(
    ! [B_7749,D_78] :
      ( r2_hidden(B_7749,k3_waybel_0('#skF_5','#skF_6'))
      | ~ r1_orders_2('#skF_5',B_7749,D_78)
      | ~ m1_subset_1(B_7749,u1_struct_0('#skF_5'))
      | ~ r2_hidden(D_78,k3_waybel_0('#skF_5','#skF_6'))
      | ~ m1_subset_1(D_78,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k3_waybel_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26,c_150106])).

tff(c_150117,plain,(
    ! [B_7751,D_7752] :
      ( r2_hidden(B_7751,k3_waybel_0('#skF_5','#skF_6'))
      | ~ r1_orders_2('#skF_5',B_7751,D_7752)
      | ~ m1_subset_1(B_7751,u1_struct_0('#skF_5'))
      | ~ r2_hidden(D_7752,k3_waybel_0('#skF_5','#skF_6'))
      | ~ m1_subset_1(D_7752,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_27783,c_150109])).

tff(c_150173,plain,
    ( r2_hidden('#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),k3_waybel_0('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_3'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),k3_waybel_0('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_3'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_140749,c_150117])).

tff(c_150291,plain,(
    r2_hidden('#skF_2'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),k3_waybel_0('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140143,c_140297,c_140298,c_150173])).

tff(c_150293,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_140606,c_150291])).

tff(c_150295,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5',k3_waybel_0('#skF_5','#skF_6'),k3_waybel_0('#skF_5','#skF_6')),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_140141])).

tff(c_150372,plain,
    ( k3_waybel_0('#skF_5',k3_waybel_0('#skF_5','#skF_6')) = k3_waybel_0('#skF_5','#skF_6')
    | ~ m1_subset_1(k3_waybel_0('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_27163,c_150295])).

tff(c_150383,plain,(
    k3_waybel_0('#skF_5',k3_waybel_0('#skF_5','#skF_6')) = k3_waybel_0('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27783,c_150372])).

tff(c_150385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_140142,c_150383])).

%------------------------------------------------------------------------------
